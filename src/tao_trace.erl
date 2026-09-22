%% Small untyped helpers for the opt-in unification tracer (core/trace):
%% environment access, per-process int counters, and ~p formatting.
%%
%% This Erlang release has removed erlang:get_env/1 and most
%% system_info items, so env vars are read via `os:cmd("printenv ...")`
%% and cached in the process dictionary.
-module(tao_trace).
-export([get_env/1, put_int/2, get_int/1, peek/1, stack/0, term/1, now/0,
         dict/0, bump/1, start_sampler/1, watch/0, spush/1, strail/0]).

get_env(Name) ->
    case erlang:get({tao_env, Name}) of
        undefined ->
            Cmd = ["printenv ", erlang:binary_to_list(Name)],
            %% printenv appends a newline; strip it (and a CR) so callers
            %% can compare values exactly.
            Value = strip_nl(erlang:iolist_to_binary(os:cmd(Cmd))),
            erlang:put({tao_env, Name}, Value),
            Value;
        Cached ->
            Cached
    end.

%% NOTE: this erlc does not accept `:binary` segment patterns; use
%% binary:part.
strip_nl(B) ->
    N = erlang:byte_size(B),
    case N of
        0 -> B;
        _ ->
            case binary:part(B, {N - 1, 1}) of
                <<10>> -> strip_nl(binary:part(B, 0, N - 1));
                _ -> B
            end
    end.

put_int(Key, Value) ->
    erlang:put(Key, Value).

get_int(Key) ->
    case erlang:get(Key) of
        undefined -> -1;
        V when is_integer(V) -> V;
        _ -> -1
    end.

peek(Key) ->
    case erlang:get(Key) of
        undefined -> 0;
        V when is_integer(V) -> V;
        _ -> 0
    end.

%% Push-only call-history trail of the last 24 instrumented function
%% entries (this BEAM truncates real stacktraces to ~7 frames, so the
%% trail is the only way to see a deep recursion cycle).
spush(Key) ->
    case erlang:get(tao_steptrail) of
        undefined -> erlang:put(tao_steptrail, [Key]);
        L when is_list(L) ->
            erlang:put(tao_steptrail, [Key | lists:sublist(L, 23)]);
        _ -> erlang:put(tao_steptrail, [Key])
    end,
    ok.

strail() ->
    case erlang:get(tao_steptrail) of
        undefined -> "";
        L when is_list(L) ->
            erlang:iolist_to_binary(
                lists:foldl(fun(K, A) -> [K, 32 | A] end, "", L));
        _ -> ""
    end.

stack() ->
    try
        Info = erlang:process_info(self(), current_stacktrace),
        Frames = element(2, Info),
        erlang:iolist_to_binary(io_lib:format("~p", [Frames]))
    catch C:R ->
        try erlang:error(probe)
        catch error:probe:Stack ->
            io:format("stack fallback ~p:~p~n", [C, R]),
            erlang:iolist_to_binary(io_lib:format("~p", [Stack]))
        end
    end.

term(Term) ->
    erlang:iolist_to_binary(io_lib:format("~p", [Term])).

now() ->
    erlang:system_time(millisecond).

dict() ->
    erlang:iolist_to_binary(
        io_lib:format("~p", [erlang:process_info(self(), dictionary)])
    ).

bump(Key) ->
    case erlang:get(Key) of
        undefined -> erlang:put(Key, 1), 1;
        N when is_integer(N) -> erlang:put(Key, N + 1), N + 1
    end.

start_sampler(Interval) ->
    spawn(fun() -> sampler_loop(Interval) end).

%% Spawn a watcher on the calling (main) process: every 2s print its
%% current location, a stack slice, and heap size. Unlike the old sampler,
%% this only ever inspects the one target process, so it cannot wedge on
%% unrelated processes.
watch() ->
    Main = erlang:self(),
    spawn(fun() ->
        watch_loop(Main, 0)
    end).

watch_loop(Main, N) ->
    case N >= 30 of
        true ->
            ok;
        false ->
            %% Small items only: stack/location items can wedge on a
            %% 100%-CPU process on this BEAM fork (nondeterministically).
            try
                Heap = erlang:process_info(Main, total_heap_size),
                MQ = erlang:process_info(Main, message_queue_len),
                io:put_chars(standard_error,
                    ["W: heap=",
                     element(2, Heap),
                     " mq=",
                     element(2, MQ), $\n]),
                ok
            catch C:R ->
                io:put_chars(standard_error,
                    ["W: err ",
                     io_lib:format("~p:~p~n", [C, R])]),
                ok
            end,
            %% receive/after is unreliable in spawned processes on this
            %% BEAM fork; busy-wait on the wall clock instead.
            wait_until(erlang:system_time(millisecond) + 2000),
            watch_loop(Main, N + 1)
    end.

wait_until(End) ->
    case erlang:system_time(millisecond) >= End of
        true -> ok;
        false -> wait_until(End)
    end.

sampler_loop(Interval) ->
    Self = erlang:self(),
    lists:foreach(
        fun(P) when P =/= Self ->
            try
                io:format("\nSAMPLER ~pms ~p~n~p~n",
                          [erlang:system_time(millisecond), P,
                           erlang:process_info(P, current_stacktrace)]),
                ok
            catch C:R -> io:format("SAMPLER ~p err ~p:~p~n", [P, C, R]), ok
            end;
         (_) -> ok
        end,
        erlang:processes()
    ),
    io:format("SLEEP-START~n"),
    receive
        after Interval -> ok
    end,
    io:format("SLEEP-END~n"),
    sampler_loop(Interval).
