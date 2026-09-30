%%% Sampling stack profiler for debugging hangs / infinite loops.
%%%
%%% Injected into the target VM by scripts/dumpstack.py, which runs:
%%%
%%%   erl +hmax <cap> -pa ... -s samplestack start -s <program> -noshell ...
%%%
%%% `start/0` is called during VM boot; it spawns several detached sampler
%%% processes and returns immediately so that boot is not delayed.
%%% Configuration is passed through environment variables:
%%%
%%%   DUMPSTACK_DELAY_MS      sleep this long before sampling starts (default 0)
%%%   DUMPSTACK_DURATION_MS   how long to sample for (default 2000)
%%%   DUMPSTACK_INTERVAL_MS   time between samples (default 100)
%%%   DUMPSTACK_LOG           file to write samples to (default: stdout)
%%%
%%% One line is printed per non-idle process per tick, e.g.:
%%%   t= 1.00s <0.5.0> depth=42  'core@normalize'/normalize/2 <- ...
%%% A tick is only printed when the set of stacks changes (identical
%%% consecutive ticks are suppressed and counted), and each sampler prints
%%% a short histogram of the most common top frames at the end.
%%%
%%% Why several sampler processes:
%%%   If a process runs a non-preemptable native loop (JIT-compiled code or
%%%   a NIF), the scheduler it is pinned to is lost forever and every
%%%   Erlang process on that scheduler stops running. A single sampler
%%%   would freeze if it happened to share the lost scheduler. With
%%%   N_SAMPLERS processes covering disjoint sets of pids, the surviving
%%%   samplers keep reporting everything except the processes owned by a
%%%   dead scheduler.
%%%
%%% Other notes:
%%%   * Output goes to the DUMPSTACK_LOG file, appended one flushed line at
%%%     a time: the target VM is terminated with SIGKILL, and anything
%%%     still in a stdout buffer would be lost.
%%%   * Each tick's process_info sweep runs in a short-lived helper with a
%%%     timeout: a process stuck in a non-preemptable native loop can block
%%%     process_info, which must not freeze the sampler.
%%%   * A process blocked in a receive is considered idle and skipped,
%%%     EXCEPT the main process (<0.0.0>): while a -s module runs during
%%%     boot the main process reports status=waiting with an
%%%     init/boot_loop stack, so filtering on status alone would hide it.
%%%   * Waiting is done by spinning on the monotonic clock, not with
%%%     timer:sleep (receive ... after T): during the real hang, timer
%%%     delivery was observed to stop firing, which froze a timer-based
%%%     sampler. A spin only depends on the scheduler giving this process
%%%     its timeslices. It does peg one core per sampler for the window,
%%%     which is expected for this tool.

-module(samplestack).
-export([start/0, sampler/5]).

-define(N_SAMPLERS, 3).  % redundant samplers, see module comment
-define(FRAMES, 4).      % stack frames kept per sample
-define(HIST, 5).        % histogram entries printed at the end

%% Called at VM boot. Spawns the samplers detached and returns immediately
%% so that boot is not delayed.
start() ->
  Delay = env_ms("DUMPSTACK_DELAY_MS", 0),
  Duration = env_ms("DUMPSTACK_DURATION_MS", 2000),
  Interval = env_ms("DUMPSTACK_INTERVAL_MS", 100),
  Log = case os:getenv("DUMPSTACK_LOG") of
    undefined -> undefined;
    "" -> undefined;
    Path -> Path
  end,
  Samplers = [spawn(samplestack, sampler,
                    [I, Delay, Duration, Interval, Log]) ||
    I <- lists:seq(0, ?N_SAMPLERS - 1)],
  %% Tell each sampler the pids of all samplers so that they do not sample
  %% each other (a spinning sampler looks "busy" and would be pure noise).
  [S ! {samplestack, Samplers} || S <- Samplers],
  ok.

sampler(Id, Delay, Duration, Interval, Log) ->
  Samplers = receive
    {samplestack, All} -> All;
    _ -> []
    after 1000 ->
      []
  end,
  open_log(Log),
  log("sampler: sampling for " ++ fmt(Duration / 1000) ++ " s at " ++
      fmt(1000 / Interval) ++ " Hz (delay " ++ fmt(Delay / 1000) ++ " s) " ++
      "[sampler " ++ integer_to_list(Id) ++ " of " ++
      integer_to_list(?N_SAMPLERS) ++ "]\n"),
  busy_wait(Delay),
  T0 = ms(),
  loop(Id, T0, T0 + Duration, Interval, 0, #{}, undefined, 0, Samplers).

%% Main sampling loop for one sampler.
loop(Id, T0, Deadline, Interval, Samples, Hist, PrevStacks, Suppressed,
     Samplers) ->
  case ms() >= Deadline of
    true ->
      summary(Id, Samples, Suppressed, Hist);
    false ->
      {Hist1, Prev1, Sup1} =
        case safe_sample(Id, Samplers, max(10, Interval div 2)) of
          {ok, Stacks} ->
            put(timeout_line, false),
            case Stacks =:= PrevStacks of
              true -> % identical tick
                {update_hist(Hist, Stacks), PrevStacks, Suppressed + 1};
              false ->
                log(lists:flatten(
                      tick_line(Id, (ms() - T0) / 1000, Stacks))),
                {update_hist(Hist, Stacks), Stacks, 0}
            end;
          timeout ->
            % Skip this tick, but say so once: this share contains a
            % process whose process_info blocks (stuck in native code).
            case get(timeout_line) of
              true -> ok;
              _ ->
                put(timeout_line, true),
                log("t=" ++ ts((ms() - T0) / 1000) ++ "s [s" ++
                    integer_to_list(Id) ++
                    "] (sample timed out: a process in this share "
                    "blocks process_info, probably stuck in native code)\n")
            end,
            {Hist, PrevStacks, Suppressed}
        end,
      busy_wait(Interval),
      loop(Id, T0, Deadline, Interval, Samples + 1, Hist1, Prev1, Sup1,
           Samplers)
  end.

%% Run sample/2 in a helper process so that a process_info call stuck on
%% a busy process cannot freeze this sampler: if the helper does not
%% report back within Timeout ms, kill it and skip this tick. (A process
%% running a non-preemptable native loop may hold its process lock, which
%% blocks process_info for other processes.)
safe_sample(Id, Samplers, Timeout) ->
  Parent = self(),
  Helper = spawn(fun() ->
    Parent ! {samplestack_sample, self(), sample(Id, Samplers)}
  end),
  receive
    {samplestack_sample, Helper, Stacks} -> {ok, Stacks}
  after Timeout ->
    exit(Helper, kill),
    timeout
  end.

%% Fetch the stacks of this sampler's share of the non-idle local
%% processes (pids are partitioned round-robin over the samplers).
%% Returns [{Pid, IsMain, Frames, Depth}]. A process waiting for a message
%% (idle) is skipped, but the main process is always included. The sampler
%% processes themselves are never sampled.
sample(Id, Samplers) ->
  Procs = erlang:processes(),
  Main = lists:min(Procs),
  Zip = lists:zip(Procs, lists:seq(1, length(Procs))),
  Found = lists:foldl(
    fun({P, I}, Acc) ->
      case (I - 1) rem ?N_SAMPLERS =:= Id of
        false -> Acc;
        true ->
          case lists:member(P, Samplers) of
            true -> Acc;
            false ->
              case erlang:process_info(P, [status, current_stacktrace]) of
                Info when is_list(Info) ->
                  % (process_info returns false for dead processes and
                  % undefined for some transient ones; skip both)
                  Status = proplists:get_value(status, Info, waiting),
                  Frames = proplists:get_value(current_stacktrace, Info, []),
                  IsMain = P =:= Main,
                  Sub = lists:sublist(Frames, ?FRAMES),
                  % Skip our own helper processes (busy or blocked while
                  % sampling, pure noise) and idle processes.
                  case is_ours(Sub) of
                    true -> Acc;
                    false ->
                      case {Sub, Status =/= waiting orelse IsMain} of
                        {[], _} -> Acc;   % no stack yet
                        {_, false} -> Acc; % idle
                        {_, true} ->
                          [{P, IsMain, Sub, length(Frames)} | Acc]
                      end
                  end;
                _ -> Acc
              end
          end
      end
    end, [], Zip),
  Found.

%% True if any of the (already truncated) frames runs samplestack code,
%% i.e. the process is one of our samplers' helpers.
is_ours(Frames) ->
  lists:any(
    fun({M, _, _}) -> M =:= samplestack;
       ({M, _, _, _}) -> M =:= samplestack;
       (_) -> false
    end, Frames).

tick_line(Id, T, []) ->
  ["t=", ts(T), "s [s", integer_to_list(Id), "] (all processes idle)\n"];
tick_line(Id, T, Stacks) ->
  [tick_entry(Id, T, S) || S <- lists:reverse(Stacks)].

tick_entry(Id, T, {P, IsMain, Frames, Depth}) ->
  ["t=", ts(T), "s [s", integer_to_list(Id), "] ", pid_to_list(P),
   case IsMain of
     true -> " (main)";
     false -> ""
   end,
   " depth=", integer_to_list(Depth), "  ", frames_str(Frames), "\n"].

ts(T) ->
  N = round(T * 100),
  [integer_to_list(N div 100), ".", case N rem 100 of
    0 -> "00";
    R -> integer_to_list(R)
  end].

frames_str(Frames) ->
  lists:join(" <- ", [frame_str(F) || F <- Frames]).

frame_str({M, F, A, _}) when is_atom(M), is_atom(F) ->
  atom_to_list(M) ++ "/" ++ atom_to_list(F) ++ "/" ++ integer_to_list(A);
frame_str({M, F, A}) when is_atom(M), is_atom(F) ->
  atom_to_list(M) ++ "/" ++ atom_to_list(F) ++ "/" ++ integer_to_list(A);
frame_str(X) ->
  io_lib:format("~p", [X]).

%% Count top frames per process for the end-of-run histogram. The main
%% process is excluded: its stack is boot scaffolding (init/boot_loop),
%% not program code, and would otherwise dominate the histogram.
update_hist(H, Stacks) ->
  lists:foldl(
    fun({_, true, _, _}, Acc) -> Acc;   % main process: excluded
       ({_, _, [], _}, Acc) -> Acc;     % no frames
       ({_, _, [Top | _], _}, Acc) ->
         case maps:find(Top, Acc) of
           {ok, N} -> maps:put(Top, N + 1, Acc);
           error -> maps:put(Top, 1, Acc)
         end
    end, H, Stacks).

summary(Id, Samples, Suppressed, Hist) ->
  S = "sampler[" ++ integer_to_list(Id) ++ "]: ",
  case Samples of
    0 ->
      log(S ++ "no ticks~n");
    _ ->
      Total = maps:fold(fun(_, N, A) -> N + A end, 0, Hist),
      Top = lists:sort(
              fun({_, N1}, {_, N2}) -> N1 >= N2 end,
              maps:to_list(Hist)),
      log(S ++ integer_to_list(Samples) ++ " samples (" ++
          integer_to_list(Suppressed) ++ " identical ticks suppressed), " ++
          "top frames across " ++ integer_to_list(Total) ++
          " non-idle stacks\n"),
      [log(io_lib:format("  ~4w  ~s~n", [N, frame_str(F)])) ||
        {F, N} <- lists:sublist(Top, ?HIST)]
  end.

%% Sleep by spinning on the monotonic clock. We deliberately avoid
%% timer:sleep (receive _ after T): during the target hang, timer
%% delivery was observed to stop firing, which froze a timer-based
%% sampler. A spin only depends on the scheduler giving this process its
%% timeslices. Note this pegs one core for the wait; that is an accepted
%% overhead for a debug tool.
busy_wait(Ms) when is_integer(Ms), Ms > 0 ->
  spin(erlang:monotonic_time(millisecond) + Ms);
busy_wait(_Ms) ->
  ok.

spin(Deadline) ->
  case erlang:monotonic_time(millisecond) of
    T when T >= Deadline -> ok;
    _ -> spin(Deadline)
  end.

%% Milliseconds from an arbitrary fixed point (fine for durations).
ms() ->
  erlang:monotonic_time(millisecond).

%% All sampler output goes through log/1. Lines are appended to the
%% DUMPSTACK_LOG file, one open/write/close per line: the close flushes, so
%% every written line survives the eventual SIGKILL, and append mode means
%% the several samplers writing to the same file do not clobber each other.
open_log(undefined) -> undefined;
open_log(Path) ->
  case file:open(Path, [append]) of
    {ok, Fd} -> file:close(Fd), put(log_path, Path), Path;
    {error, enoent} ->
      case file:open(Path, [write]) of
        {ok, Fd2} ->
          file:close(Fd2),
          put(log_path, Path),
          Path;
        {error, Reason} ->
          io:format("sampler: cannot open log file ~s: ~p (using stdout)~n",
                    [Path, Reason]),
          undefined
      end;
    {error, Reason} ->
      io:format("sampler: cannot open log file ~s: ~p (using stdout)~n",
                [Path, Reason]),
      undefined
  end.

log(S) when is_list(S) ->
  case get(log_path) of
    undefined -> io:put_chars(S);
    Path ->
      case file:open(Path, [append]) of
        {ok, Fd} ->
          file:write(Fd, S),
          file:close(Fd);
        {error, _} -> io:put_chars(S)
      end
  end.

fmt(X) ->
  io_lib:format("~.2f", [X]).

env_ms(Name, Default) ->
  case os:getenv(Name) of
    undefined -> Default;
    V ->
      try list_to_integer(V) of
        N when is_integer(N) -> N
      catch _:_ -> Default
      end
  end.
