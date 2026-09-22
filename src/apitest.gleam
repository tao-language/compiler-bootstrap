/// Scratch probe: verify step counters/heartbeat on this BEAM.
import core/step.{step}
import gleam/int
import gleam/io

@external(erlang, "tao_trace", "get_int")
fn pget(key: String) -> Int

@external(erlang, "tao_trace", "get_env")
fn env_str(name: String) -> String

@external(erlang, "tao_trace", "watch")
fn pwatch() -> Nil

pub fn maybe() {
  case env_str("TAO_WATCH") {
    "" -> Nil
    _ -> pwatch()
  }
  case env_str("TAO_STEP_TEST") {
    "" -> Nil
    _ -> {
      case env_str("TAO_DICT_TEST") {
        "hb" -> hb_test()
        _ -> dict_probe()
      }
      io.println_error("probe: exiting")
      exit(0)
    }
  }
}

fn hb_test() {
  probe_loop(0, 200)
  busy(3200)
  io.println_error(
    "-- waking now=" <> int.to_string(pnow())
      <> " hbkey="
      <> int.to_string(pget("tao_step_hb")),
  )
  step("hbtest")
}

@external(erlang, "tao_trace", "put_int")
fn pput(key: String, value: Int) -> Nil

@external(erlang, "erlang", "halt")
fn exit(status: Int) -> Nil

@external(erlang, "tao_trace", "now")
fn pnow() -> Int

fn busy(ms: Int) {
  let t0 = pnow()
  busy_loop(t0 + ms)
}

fn busy_loop(end: Int) {
  case pnow() >= end {
    True -> Nil
    False -> busy_loop(end)
  }
}

pub fn dict_probe() {
  pput("ktest", 111)
  busy(100)
  io.println_error("read1=" <> int.to_string(pget("ktest")))
  pput("ktest", 222)
  busy(100)
  io.println_error("read2=" <> int.to_string(pget("ktest")))
  io.println_error("read3=" <> int.to_string(pget("ktest")))
}

pub fn probe() {
  probe_loop(0, 5000)
  io.println_error(
    "probe done counter=" <> int.to_string(pget("probe")),
  )
}

fn probe_loop(i: Int, to: Int) {
  case i >= to {
    True -> Nil
    False -> {
      step("probe")
      case i % 1000 == 0 {
        True -> io.println_error("probe i=" <> int.to_string(i))
        False -> Nil
      }
      probe_loop(i + 1, to)
    }
  }
}
