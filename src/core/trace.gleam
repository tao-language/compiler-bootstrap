/// Opt-in unification tracing for hang debugging (stderr only).
///
/// Enable with `TAO_TRACE=unify` (retry markers + `unify:*` step counters)
/// or `TAO_TRACE_ALL=1`. Finer channels, via `TAO_TRACE=<channel>`:
/// * `unify:solves` — one `S:` line per hole solve (capped at 300) plus
///   store-path diagnostics (`T:` selfref accepted, `R:` refused, `O:`
///   open-hole store, `M:` merge);
/// * `unify:deferred` — the deferred queue after every retry;
/// * `unify:anchor` — a frame-diff histogram of hole re-anchors, printed
///   once per retry;
/// * every `retry_deferred` pass prints one `U:` line: retry number,
///   queue size in/out, hole counter, solved-hole count, and a
///   fingerprint of the solved hole ids; on the first retry whose hole
///   counter reaches `TAO_TRACE_DUMP` (default 100) the full substitution
///   table is dumped once, and on the `TAO_TRACE_STACK`-th retry (default
///   300) the innermost call stack is printed once.
///
/// All markers go to stderr so they never interleave with the phase
/// output on stdout.
import core/context.{type Context}
import core/format
import core/step
import core/value.{type Env, type Value}
import gleam/int
import gleam/io
import gleam/list
import gleam/string

@external(erlang, "tao_trace", "get_env")
fn env_str(name: String) -> String

@external(erlang, "tao_trace", "put_int")
fn pput(key: String, value: Int) -> Nil

@external(erlang, "tao_trace", "get_int")
fn pget(key: String) -> Int

@external(erlang, "tao_trace", "stack")
fn pstack() -> String

@external(erlang, "tao_trace", "dict")
fn pdict() -> String


const key_counter = "tao_unify_retries"

const key_dumped = "tao_unify_dumped"

const key_stacked = "tao_unify_stacked"

fn env_value(name: String) -> String {
  string.trim_end(env_str(name))
}

pub fn enabled() -> Bool {
  step.channel_on("unify", "default")
}

fn int_env(name: String, default: Int) -> Int {
  case int.parse(env_value(name)) {
    Ok(n) -> n
    Error(_) -> default
  }
}

fn counter(key: String) -> #(Int, Int) {
  let n = int.max(0, pget(key))
  pput(key, n + 1)
  #(n, n + 1)
}

fn once(key: String) -> Bool {
  let done = pget(key) >= 0
  case done {
    True -> False
    False -> {
      pput(key, 1)
      True
    }
  }
}

/// Print the one-shot substitution dump: every solved hole with its
/// captured env length and solution value, plus the deferred queue size.
pub fn dump_subst(ctx: Context, reason: String) {
  case once(key_dumped) {
    False -> Nil
    True -> {
      io.println_error("// UNIFY DUMP " <> reason)
      io.println_error(
        "// holes="
          <> int.to_string(ctx.hole_counter)
          <> " subst="
          <> int.to_string(list.length(ctx.subst))
          <> " deferred="
          <> int.to_string(list.length(ctx.deferred)),
      )
      let names = list.map(ctx.types, fn(entry) { entry.0 })
      let subst = list.sort(ctx.subst, fn(a, b) { int.compare(a.0, b.0) })
      let _ =
        list.map(subst, fn(entry) {
          let #(id, #(env, value)) = entry
          let formatted =
            format.value(ctx.ffi, names, value, 120, 3) |> string.slice(0, 300)
          io.println_error(
            "h"
              <> int.to_string(id)
              <> " (envlen="
              <> int.to_string(list.length(env))
              <> "): "
              <> formatted,
          )
        })
      Nil
    }
  }
}

/// Accumulate a frame-diff histogram (keyed by ref_len/solve_len and the
/// common outer suffix length) when the `unify:anchor` channel is on; the
/// histogram is printed once per `retry_deferred` pass (see `anchor_dump`).
pub fn anchor(_hole_id: Int, ref_env: Env, solve_env: Env) {
  case step.channel_on("unify", "anchor") {
    False -> Nil
    True -> {
      let key = "anchor|" <> int.to_string(list.length(ref_env))
        <> "|" <> int.to_string(list.length(solve_env))
        <> "|" <> int.to_string(common_suffix(ref_env, solve_env))
      pput(key, int.max(0, pget(key)) + 1)
    }
  }
}

/// Print the accumulated frame-diff histogram (cleared afterwards).
pub fn anchor_dump() {
  case step.channel_on("unify", "anchor") {
    False -> Nil
    True -> io.println_error("A: " <> pdict())
  }
}

/// Print the deferred queue (one line per pair) when the `unify:deferred`
/// channel is on, at most every `TAO_TRACE_DEFERRED_EVERY` retries
/// (default: every one).
pub fn deferred_dump(ctx: Context) {
  case step.channel_on("unify", "deferred") {
    False -> Nil
    True -> {
      let n = int.max(0, pget(key_deferred_n))
      pput(key_deferred_n, n + 1)
      let every = int_env("TAO_TRACE_DEFERRED_EVERY", 1)
      let q = list.length(ctx.deferred)
      case every > 0 {
        False -> Nil
        True -> case q > 200 || n % every == 0 {
        True -> {
          let names = list.map(ctx.types, fn(entry) { entry.0 })
          io.println_error(
            "D: queue=" <> int.to_string(list.length(ctx.deferred))
              <> " (retry " <> int.to_string(n) <> ")",
          )
          let _ =
            list.index_map(ctx.deferred, fn(pair, i) {
              let #(#(a, _sa), #(b, _sb)) = pair
              io.println_error(
                "  d" <> int.to_string(i) <> ": ["
                  <> string.slice(format.value(ctx.ffi, names, a, 120, 2), 0, 160)
                  <> "] vs ["
                  <> string.slice(format.value(ctx.ffi, names, b, 120, 2), 0, 160)
                  <> "]",
              )
            })
          Nil
        }
        False -> Nil
      }
      }
    }
  }
}

const key_deferred_n = "tao_unify_deferred_n"

/// Length of the longest common outer suffix of the two frames, or -1
/// when nothing matches from the innermost end.
fn common_suffix(a: Env, b: Env) -> Int {
  let la = list.length(a)
  let lb = list.length(b)
  let n = int.min(la, lb)
  let asuffix = list.take(list.reverse(a), n)
  let bsuffix = list.take(list.reverse(b), n)
  case asuffix == bsuffix {
    True -> n
    False -> {
      let i = first_diff(asuffix, bsuffix, 0)
      case i {
        -1 -> -1
        _ -> i
      }
    }
  }
}

fn first_diff(a: List(Value), b: List(Value), i: Int) -> Int {
  case a, b {
    [], [] -> -1
    [x, ..xs], [y, ..ys] -> case x == y {
      True -> first_diff(xs, ys, i + 1)
      False -> i
    }
    _, _ -> -1
  }
}

/// Print the one-shot call stack (names the cycle re-entering unification).
pub fn dump_stack(n: Int) {
  case once(key_stacked) {
    False -> Nil
    True -> {
      io.println_error("// UNIFY STACK (retry #" <> int.to_string(n) <> ")")
      io.println_error(pstack())
    }
  }
}

/// Log one hole solve with the solution's shape when the `unify:solves`
/// channel is on (capped at 300 lines).
pub fn solve(ctx: Context, hole_id: Int, value: Value) {
  case step.channel_on("unify", "solves") {
    False -> Nil
    True -> {
      let n = int.max(0, pget(key_solves_n))
      pput(key_solves_n, n + 1)
      case n >= 300 {
        True -> Nil
        False -> {
          let names = list.map(ctx.types, fn(entry) { entry.0 })
          io.println_error(
            "S: h" <> int.to_string(hole_id)
              <> " (envlen=" <> int.to_string(list.length(ctx.env))
              <> "): "
              <> string.slice(format.value(ctx.ffi, names, value, 100, 2), 0, 160),
          )
        }
      }
    }
  }
}



const key_solves_n = "tao_unify_solves_n"

/// Log one store-path diagnostic line (open-hole store, merge, refused
/// solve) when the `unify:solves` channel is on; capped separately from
/// the S: log.
pub fn solve_note(line: String) {
  case step.channel_on("unify", "solves") {
    False -> Nil
    True -> {
      let n = int.max(0, pget(key_note_n))
      pput(key_note_n, n + 1)
      case n >= 500 {
        True -> Nil
        False -> io.println_error(line)
      }
    }
  }
}

const key_note_n = "tao_unify_note_n"

/// One marker per `retry_deferred` pass, plus the one-shot dumps.
pub fn retry(ctx: Context, queue_in: Int, queue_out: Int, newholes: Int) {
  case enabled() {
    False -> Nil
    True -> {
      let #(n, _) = counter(key_counter)
      let fp =
        list.map(ctx.subst, fn(entry) { entry.0 })
        |> list.sort(int.compare)
      io.println_error(
        "Q: retry #"
          <> int.to_string(n)
          <> " in="
          <> int.to_string(queue_in)
          <> " out="
          <> int.to_string(queue_out)
          <> " holes="
          <> int.to_string(ctx.hole_counter)
          <> " subst="
          <> int.to_string(list.length(ctx.subst))
          <> " +newholes="
          <> int.to_string(newholes)
          <> " cnt="
          <> int.to_string(step.step_count("context:new_hole"))
          <> " fp=["
          <> string.join(list.map(fp, int.to_string), ",")
          <> "]",
      )
      anchor_dump()
      deferred_dump(ctx)
      let dump_at = int_env("TAO_TRACE_DUMP", 100)
      let stack_at = int_env("TAO_TRACE_STACK", 300)
      // A `case` in block position is discarded; run the last one first so it
      // actually executes, and gate the dumps on its result.
      case ctx.hole_counter >= dump_at {
        True -> {
          case n >= stack_at {
            True -> {
              dump_subst(ctx, "holes>=" <> int.to_string(dump_at))
              dump_stack(n)
            }
            False -> dump_subst(ctx, "holes>=" <> int.to_string(dump_at))
          }
        }
        False -> case n >= stack_at {
          True -> dump_stack(n)
          False -> Nil
        }
      }
    }
  }
}
