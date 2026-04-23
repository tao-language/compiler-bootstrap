// ============================================================================
// EXIT CODE
// ============================================================================
/// Exit the process with a given exit code.
/// Uses Erlang's erlang:halt/1 via external function.

/// Exit with the given code. 0 means success, non-zero means failure.
@external(erlang, "erlang", "halt")
pub fn exit(code: Int) -> Nil
