// ============================================================================
// COLOR TESTS
// ============================================================================
/// Tests for ANSI color support.

import core/color
import gleam/string
import gleeunit
import gleeunit/should

pub fn main() {
  gleeunit.main()
}

// ============================================================================
// COLOR CONSTANTS
// ============================================================================

pub fn reset_contains_esc_test() {
  color.reset |> string.starts_with("\u{1b}[") |> should.be_true
  color.reset |> string.contains("0m")
}

pub fn red_contains_esc_test() {
  color.red |> string.starts_with("\u{1b}[") |> should.be_true
  color.red |> string.contains("31m")
}

pub fn green_contains_esc_test() {
  color.green |> string.starts_with("\u{1b}[") |> should.be_true
  color.green |> string.contains("32m")
}

pub fn bold_contains_esc_test() {
  color.bold |> string.starts_with("\u{1b}[") |> should.be_true
  color.bold |> string.contains("1m")
}

// ============================================================================
// COLOR CONFIGURATION
// ============================================================================

pub fn default_config_enabled_test() {
  color.default_config.enabled |> should.be_true
  color.default_config.force |> should.be_false
}

pub fn no_color_config_test() {
  color.no_color.enabled |> should.be_false
  color.no_color.force |> should.be_false
}

pub fn should_use_colors_enabled_test() {
  color.should_use_colors(color.default_config) |> should.be_true
}

pub fn should_use_colors_disabled_test() {
  color.should_use_colors(color.no_color) |> should.be_false
}

pub fn should_use_colors_forced_test() {
  let forced = color.ColorConfig(enabled: False, force: True)
  color.should_use_colors(forced) |> should.be_true
}

// ============================================================================
// COLORIZE
// ============================================================================

pub fn colorize_enabled_test() {
  let result = color.colorize("hello", color.red, color.default_config)
  result |> string.starts_with(color.red) |> should.be_true
  result |> string.ends_with(color.reset) |> should.be_true
  result |> string.contains("hello") |> should.be_true
}

pub fn colorize_disabled_test() {
  let result = color.colorize("hello", color.red, color.no_color)
  result |> should.equal("hello")
}

pub fn colorize_bold_test() {
  let result = color.colorize_bold("error", color.default_config)
  result |> string.starts_with(color.bold) |> should.be_true
  result |> string.contains("error") |> should.be_true
}

pub fn colorize_red_test() {
  let result = color.colorize_red("error", color.default_config)
  result |> string.starts_with(color.red) |> should.be_true
}

pub fn colorize_green_test() {
  let result = color.colorize_green("ok", color.default_config)
  result |> string.starts_with(color.green) |> should.be_true
}

// ============================================================================
// ERROR SPECIFIC HELPERS
// ============================================================================

pub fn colorize_error_header_test() {
  let result = color.colorize_error_header("Error", color.default_config)
  result |> string.starts_with(color.bright_red) |> should.be_true
  result |> string.starts_with(color.bright_red <> color.bold) |> should.be_true
}

pub fn colorize_warning_header_test() {
  let result = color.colorize_warning_header("Warning", color.default_config)
  result |> string.starts_with(color.bright_yellow <> color.bold) |> should.be_true
}

pub fn colorize_tip_test() {
  let result = color.colorize_tip("tip", color.default_config)
  result |> string.starts_with(color.cyan) |> should.be_true
}

// ============================================================================
// STRIP ANSI CODES
// ============================================================================

pub fn strip_ansi_codes_removes_escapes_test() {
  let colored = color.colorize("hello", color.red, color.default_config)
  let plain = color.strip_ansi_codes(colored)
  plain |> should.equal("hello")
}

pub fn strip_ansi_codes_no_color_test() {
  let plain = "hello world"
  let result = color.strip_ansi_codes(plain)
  result |> should.equal(plain)
}

pub fn strip_ansi_codes_disabled_color_test() {
  let no_color = color.colorize("hello", color.red, color.no_color)
  let result = color.strip_ansi_codes(no_color)
  result |> should.equal("hello")
}
