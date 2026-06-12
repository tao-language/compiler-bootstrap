import core/value.{env_push, float_t, int_t, var}

pub fn env_push_vars_empty_env_test() {
  assert env_push([], 3) == [var(2), var(1), var(0)]
}

pub fn env_push_vars_non_empty_env_test() {
  let env0 = [int_t, float_t]
  assert env_push(env0, 3) == [var(4), var(3), var(2), ..env0]
}
