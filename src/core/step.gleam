/// Step counters with per-module trace control (opt-in, stderr only).
///
/// `step("module:function")` counts invocations of that function and, while
/// the module's trace is enabled, prints:
/// * an `S2 <key>=<n>` line every 500 calls (with wall-clock state),
/// * an `HB <key>=<n>` line at most once per 3 s (names the function still
///   running at any moment, including the moment of a hang),
/// * a `// STEP <key> reached <n>` line plus the innermost call stack every
///   `TAO_TRACE_STEP` calls (default 200000).
///
/// Traces are disabled by default. `TAO_TRACE=eval,unify,...` enables the
/// listed modules only; `TAO_TRACE_ALL=1` enables every module.
/// This module must stay a leaf (stdlib imports only).
import gleam/int
import gleam/io
import gleam/list
import gleam/string

@external(erlang, "tao_trace", "get_env")
fn env_str(name: String) -> String

@external(erlang, "tao_trace", "bump")
fn pbump(key: String) -> Int

@external(erlang, "tao_trace", "peek")
fn ppeek(key: String) -> Int

@external(erlang, "tao_trace", "spush")
fn pspush(key: String) -> Nil

@external(erlang, "tao_trace", "strail")
fn pstrail() -> String

@external(erlang, "tao_trace", "stack")
fn pstack() -> String

@external(erlang, "tao_trace", "start_sampler")
fn psampler(interval: Int) -> Nil

@external(erlang, "tao_trace", "now")
fn pnow() -> Int

@external(erlang, "tao_trace", "get_int")
fn pget_int(key: String) -> Int

@external(erlang, "tao_trace", "put_int")
fn pput_int(key: String, value: Int) -> Nil

/// Start the call-stack sampler when `TAO_TRACE_SAMPLER` (interval ms,
/// default 5000) is set; prints the target's call stack periodically.
fn maybe_sample() {
  case env_value("TAO_TRACE_SAMPLER") {
    "" -> Nil
    _ -> {
      let interval = case int.parse(env_value("TAO_TRACE_SAMPLER")) {
        Ok(n) -> n
        Error(_) -> 5000
      }
      case pbump("tao_sampler_started") {
        1 -> psampler(interval)
        _ -> Nil
      }
    }
  }
}

pub fn step(key: String) {
  case module_on(module_of(key)) {
    False -> Nil
    True -> {
      maybe_sample()
      pspush(key)
      let at = case int.parse(env_value("TAO_TRACE_STEP")) {
        Ok(n) -> int.max(1, n)
        Error(_) -> 200_000
      }
      let n = pbump(key)
      heartbeat(key, n)
      let s2 = case int.parse(env_value("TAO_TRACE_S2")) {
        Ok(m) -> int.max(1, m)
        Error(_) -> 500
      }
      case n % s2 == 0 {
        True -> io.println_error("S2 " <> key <> "=" <> int.to_string(n))
        False -> Nil
      }
      case n % at == 0 {
        True -> {
          io.println_error("// STEP " <> key <> " reached " <> int.to_string(n))
          io.println_error(pstrail())
          io.println_error(pstack())
        }
        False -> Nil
      }
    }
  }
}

/// Whether all module traces are on (`TAO_TRACE_ALL=1`).
pub fn all_on() -> Bool {
  env_value("TAO_TRACE_ALL") != ""
}

/// Whether the `TAO_TRACE` token list enables `mod`.
pub fn module_on(mod: String) -> Bool {
  case all_on() {
    True -> True
    False -> {
      let toks = env_value("TAO_TRACE")
      case toks {
        "" -> False
        _ -> list.contains(tokens(toks), mod)
      }
    }
  }
}

/// The current value of a step counter (without incrementing it).
pub fn step_count(key: String) -> Int {
  ppeek(key)
}

/// Whether the `TAO_TRACE` token list enables the sub-channel `mod:sub`;
/// a bare module token also enables that module's `default` sub-channel.
pub fn channel_on(mod: String, sub: String) -> Bool {
  case all_on() {
    True -> True
    False -> {
      let toks = tokens(env_value("TAO_TRACE"))
      let exact = list.contains(toks, mod <> ":" <> sub)
      let default = sub == "default" && list.contains(toks, mod)
      exact || default
    }
  }
}

fn tokens(csv: String) -> List(String) {
  string.split(csv, ",")
  |> list.map(string.trim)
  |> list.filter(fn(t) { t != "" })
}

fn module_of(key: String) -> String {
  case string.split_once(key, ":") {
    Ok(#(mod, _)) -> mod
    Error(_) -> key
  }
}

fn env_value(name: String) -> String {
  string.trim_end(env_str(name))
}

/// Time-gated marker: while the module trace is on, at most one line per
/// 3 s prints the key of the step being counted and its count so far, so
/// a hung run shows which instrumented functions are still being called at
/// the moment of the kill.
fn heartbeat(key: String, count: Int) {
  let now = pnow()
  let last = pget_int("tao_step_hb")
  case count % 2000 == 0 {
    True ->
      io.println_error(
        "HBD " <> key <> " now=" <> int.to_string(now)
          <> " last="
          <> int.to_string(last),
      )
    False -> Nil
  }
  case now - last >= 3000 {
    True -> {
      pput_int("tao_step_hb", now)
      io.println_error(
        "HB " <> key <> "=" <> int.to_string(count) <> " trail: " <> pstrail(),
      )
    }
    False -> Nil
  }
}
