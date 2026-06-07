import core/value.{env_push_vars, float_t, int_t, var}
import gleam/option.{None, Some}
import gleeunit

pub fn main() {
  gleeunit.main()
}

pub fn env_push_vars_empty_env_test() {
  assert env_push_vars([], 3) == [var(2), var(1), var(0)]
}

pub fn env_push_vars_non_empty_env_test() {
  let env0 = [int_t, float_t]
  assert env_push_vars(env0, 3) == [var(4), var(3), var(2), ..env0]
}
