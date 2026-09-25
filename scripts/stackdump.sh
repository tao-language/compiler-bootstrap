#!/usr/bin/env bash
# Stack-dump a hanging compiler run on the BEAM.
#
# The BEAM scheduler is preemptive, so even a busy-looping process can be
# sampled by another one: a spawned tracer periodically calls
# erlang:process_display(Pid, stack) on the process running the CLI and
# prints its call stack, stack size, heap size and reduction delta. That
# locates a hang (or exponential blow-up: the reduction delta between dumps
# shows the spin rate) without any instrumentation in the Gleam source.
#
# Works with any CLI command of the main program:
#   scripts/stackdump.sh -- debug-file --add=prelude lib/prelude/v0.0.1/result.tao
#   scripts/stackdump.sh -- test lib/prelude/v0.0.1/result.tao
#
# Options:
#   --interval MS  dump period in ms (default 500)
#   --max N        halt the VM after N dumps (default 12)
#
# Notes on this Erlang build (homebrew 29.0.6): the erl -eval path routes
# remote calls through a broken erlang:apply and ignores colon-separated
# -pa lists, so main is started from a compiled launcher beam (with the CLI
# args embedded as a literal term) and each ebin gets its own -pa flag.

set -euo pipefail
cd "$(dirname "$0")/.."

INTERVAL=500
MAX=12
while [ $# -gt 0 ]; do
  case "$1" in
    --interval) INTERVAL="$2"; shift 2 ;;
    --max) MAX="$2"; shift 2 ;;
    --) shift; break ;;
    *) break ;;
  esac
done
[ $# -gt 0 ] || { echo "stackdump.sh: no CLI args after --" >&2; exit 2; }
CLI_ARGS=("$@")

gleam build --target erlang >/dev/null 2>&1 || gleam build >/dev/null

TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT

# The launcher: a compiled beam calling the CLI entrypoint directly, with
# the args embedded (the eval path and os:argv/-extra are broken here).
# entrypoint/1 matches binaries (~"..." in Gleam), so args are binaries.
ERL_BINS=""
for a in "${CLI_ARGS[@]}"; do
  esc=${a//\"/\\\"}
  ERL_BINS+="<<\"$esc\">>, "
done
cat > "$TMP/sd_run.erl" <<EOF
-module(sd_run).
-export([go/0]).
go() ->
  'cli@entrypoint':entrypoint([${ERL_BINS%, }]).
EOF
erlc -o "$TMP" "$TMP/sd_run.erl"

# The tracer: samples the main process's call stack on a timer.
cat > "$TMP/sd.erl" <<'EOF'
-module(sd).
-export([start/3]).

start(Pid, Interval, Max) ->
  spawn(fun() -> loop(Pid, 1, Interval, erlang:monotonic_time(millisecond), 0, Max) end).

loop(Pid, N, Interval, PrevNow, PrevRed, Max) ->
  % process_info/2 with an item list is broken in this Erlang build.
  Info = erlang:process_info(Pid),
  Ss = proplists:get_value(current_stacksize, Info),
  Hp = proplists:get_value(total_heap_size, Info),
  Rd = proplists:get_value(reductions, Info),
  Dt = erlang:monotonic_time(millisecond) - PrevNow,
  case erlang:process_display(Pid, stack) of
    {stack, Stk} ->
      Fs = lists:map(
        fun({_, Mfa, {L, _Locals}}) ->
          {M, F, A} = Mfa, io_lib:format("~s:~s/~b@~b", [M, F, A, L])
        end, lists:sublist(Stk, 12)),
      Dots = if length(Stk) > 12 -> ["..."]; true -> [] end,
      io:format("[t+~bms #~b] stack=~b heap=~b red+~b | ~s~n",
                [Dt, N, Ss, Hp, Rd - PrevRed, string:join(Fs ++ Dots, " <- ")]);
    _ ->
      io:format("[t+~bms #~b] stack=~b heap=~b red+~b | <no stack>~n",
                [Dt, N, Ss, Hp, Rd - PrevRed])
  end,
  case N >= Max of
    true -> erlang:halt(9);
    false ->
      timer:sleep(Interval),
      loop(Pid, N + 1, Interval, erlang:monotonic_time(millisecond), Rd, Max)
  end.
EOF
erlc -o "$TMP" "$TMP/sd.erl"

# This Erlang build ignores colon-separated -pa lists, so pass one -pa
# flag per ebin directory.
PA_ARGS=()
PA_ARGS+=("-pa" "$TMP")
while IFS= read -r ebin; do
  PA_ARGS+=("-pa" "$ebin")
done < <(find build/dev/erlang -type d -name ebin)

timeout -k 9 15 erl -noshell -name "sd_$RANDOM" \
  "${PA_ARGS[@]}" \
  -eval "sd:start(self(), $INTERVAL, $MAX)" \
  -eval 'sd_run:go()'
