%% Busy-poll in-VM sampler for stackdump.py (spawned by the generated
%% launcher beam).
%%
%% Two tracers busy-poll and, every Iters poll iterations, append one
%% line per tracer to the log file:
%%   [#N trI] {Module,Function,Arity} <0.123.0> | red+DELTA heap=SIZE msq=LEN
%%
%% Target selection (Target is the launcher pid or the atom scan):
%%   - launcher pid: sample that one process. In CLI mode the launcher
%%     runs the whole program itself, so this is exact and cheap.
%%   - scan: the spin may be in any process (eunit runs `gleam test`
%%     functions in spawned task processes), so each sample scans all VM
%%     processes and reports the one with the biggest reduction delta
%%     since the previous sample - the infinite loop always dominates.
%%     The sampler's own processes (passed via the skip message) are
%%     skipped.
%%
%% Sampling is by iteration count, NOT by time: erlang:monotonic_time
%% runs at an arbitrary rate (sometimes backwards) in this Erlang build,
%% so time-based deadlines never fire. The period is therefore
%% workload-dependent. The tracers are best-effort: under very heavy
%% target workloads they can be starved. See docs/erlang-gotchas.md.
%%
%% The top frame comes from the full process_info dict:
%% erlang:process_display/2 and erlang:trace/3 [call] are broken in
%% this build. A process stuck in one long C call shows the MFA of the
%% function that made the C call; pair with the native sample to see
%% the C side.
%%
%% Halts the VM: 9 after Max samples, 1 if the launcher dies first.
%% io:format from here would be lost when the VM dies (buffered stdio),
%% so all output goes to the log file (immediate file port writes).
%% file:write/2 returns {error,badarg} silently for non-list terms, so
%% only ever pass iolists.

-module(stackdump).
-export([start/5, run/6, watch/2, loop/2, sample/10, do_sample/8,
         candidates/3, handle_info/5, pick_best/3, pget/2, flog/2]).

start(Launcher, Target, Iters, Max, Log) ->
  flog(Log, io_lib:format("stackdump: launcher ~p, target ~p, ~b samples every ~b iterations~n",
                          [Launcher, Target, Max, Iters])),
  T1 = spawn(?MODULE, run, [Launcher, Target, 1, Iters, Max, Log]),
  T2 = spawn(?MODULE, run, [Launcher, Target, 2, Iters, Max, Log]),
  W = spawn(?MODULE, watch, [[T1, T2], Log]),
  Skip = [T1, T2, W],
  T1 ! {skip, Skip},
  T2 ! {skip, Skip},
  ok.

watch(Pids, Log) ->
  Ms = [erlang:monitor(process, P) || P <- Pids],
  loop(Ms, Log).

loop(Ms, Log) ->
  receive
    {'DOWN', M, process, P, Reason} ->
      flog(Log, io_lib:format("watch: ~p DOWN ~p~n", [P, Reason])),
      Ms2 = [X || X <- Ms, element(1, X) =/= M],
      case Ms2 of
        [] -> ok;
        _ -> loop(Ms2, Log)
      end
  end.

run(Launcher, Target, Id, Iters, Max, Log) ->
  receive {skip, Skip} -> ok end,
  flog(Log, io_lib:format("tr~b started~n", [Id])),
  sample(Launcher, Target, Id, Iters, Max, Log, 1, 0, [], Skip).

sample(Launcher, Target, Id, Iters, Max, Log, N, Cnt, PrevMap, Skip) ->
  Cnt2 = Cnt + 1,
  case Cnt2 >= Iters of
    true ->
      try
        Map2 = do_sample(Launcher, Target, Id, Max, Log, N, PrevMap, Skip),
        sample(Launcher, Target, Id, Iters, Max, Log, N + 1, 0, Map2, Skip)
      catch Class:Reason:_ ->
        flog(Log, io_lib:format("tr~b CRASH: ~p:~p~n", [Id, Class, Reason])),
        sample(Launcher, Target, Id, Iters, Max, Log, N, 0, PrevMap, Skip)
      end;
    false ->
      sample(Launcher, Target, Id, Iters, Max, Log, N, Cnt2, PrevMap, Skip)
  end.

do_sample(Launcher, Target, Id, Max, Log, N, PrevMap, Skip) ->
  case lists:member(Launcher, erlang:processes()) of
    false ->
      flog(Log, "stackdump: launcher gone, halting~n"),
      erlang:halt(1);
    true ->
      case Target of
        scan ->
          All = erlang:processes(),
          Cands = candidates(Skip, All, []),
          Map = [{P, Rd} || {P, Rd, _, _, _} <- Cands],
          case pick_best(Cands, PrevMap, none) of
            none -> Map;
            {Pid, Delta, Cur, Hp, Mq} ->
              emit(Id, Max, Log, N, Cur, Pid, Delta, Hp, Mq, Map)
          end;
        Pid ->
          case erlang:process_info(Pid) of
            [] ->
              flog(Log, "stackdump: target gone, halting~n"),
              erlang:halt(1);
            undefined -> PrevMap;
            Info ->
              Cur = pget(Info, current_function),
              Rd = pget(Info, reductions),
              Hp = pget(Info, total_heap_size),
              Mq = pget(Info, message_queue_len),
              Prev =
                case lists:keyfind(Pid, 1, PrevMap) of
                  false -> Rd;
                  {_, R0} -> R0
                end,
              emit(Id, Max, Log, N, Cur, Pid, Rd - Prev, Hp, Mq, [{Pid, Rd}])
          end
      end
  end.

emit(Id, Max, Log, N, Cur, Pid, Delta, Hp, Mq, Map) ->
  flog(Log, io_lib:format("[#~b tr~b] ~p ~p | red+~b heap=~b msq=~b~n",
                          [N, Id, Cur, Pid, Delta, Hp, Mq])),
  case N >= Max of
    true -> erlang:halt(9);
    false -> Map
  end.

%% One tuple per live readable process: {Pid, Reductions, Cur, Heap, Mq}.
%% process_info/1 in this Erlang build returns undefined (not []) for
%% processes blocked in a timer wait (receive after), so those are
%% skipped for this round; an executing process is always readable and
%% that is where a spin would be.
candidates(_, [], Acc) -> Acc;
candidates(Skip, [P | Ps], Acc) ->
  case lists:member(P, Skip) of
    true -> candidates(Skip, Ps, Acc);
    false ->
      case erlang:process_info(P) of
        [] -> candidates(Skip, Ps, Acc);
        undefined -> candidates(Skip, Ps, Acc);
        Info -> handle_info(Skip, P, Ps, Info, Acc)
      end
  end.

handle_info(Skip, P, Ps, Info, Acc) ->
  try
    Cur = pget(Info, current_function),
    case Cur of
      {?MODULE, _, _} -> candidates(Skip, Ps, Acc);
      _ ->
        Rd = pget(Info, reductions),
        Hp = pget(Info, total_heap_size),
        Mq = pget(Info, message_queue_len),
        candidates(Skip, Ps, [{P, Rd, Cur, Hp, Mq} | Acc])
    end
  catch _:_ ->
    candidates(Skip, Ps, Acc)
  end.

pick_best([], _PrevMap, Best) -> Best;
pick_best([{P, Rd, Cur, Hp, Mq} | Rest], PrevMap, Best) ->
  Prev =
    case lists:keyfind(P, 1, PrevMap) of
      false -> Rd;
      {_, R0} -> R0
    end,
  This = {P, Rd - Prev, Cur, Hp, Mq},
  case Best of
    none -> pick_best(Rest, PrevMap, This);
    {_, D, _, _, _} ->
      case element(2, This) > D of
        true -> pick_best(Rest, PrevMap, This);
        false -> pick_best(Rest, PrevMap, Best)
      end
  end.

%% Total by construction: process_info/1 can return non-lists in this
%% build, which make both proplists:get_value and lists:keyfind raise.
pget(Info, Key) ->
  case is_list(Info) of
    false -> undefined;
    true ->
      try
        case lists:keyfind(Key, 1, Info) of
          false -> undefined;
          {_, V} -> V
        end
      catch _:_ -> undefined
      end
  end.

flog(Log, Line) ->
  case file:open(Log, [write, append]) of
    {ok, Fd} -> file:write(Fd, Line), file:close(Fd);
    {error, R} ->
      case file:open("/tmp/stackdump-flog.err", [write, append]) of
        {ok, Fd2} ->
          file:write(Fd2, io_lib:format("flog ~p failed: ~p~n", [Line, R])),
          file:close(Fd2);
        _ -> ok
      end
  end.
