// ============================================================================
// ANSI COLOR SUPPORT
// ============================================================================
/// Terminal color support using ANSI escape codes.
///
/// Provides colorized output for error messages and other terminal output.
/// Colors can be enabled/disabled via configuration.
import gleam/string

// ============================================================================
// ANSI COLOR CODES
// ============================================================================

/// ANSI escape code prefix (ESC character)
const esc = "\u{1b}["

/// Reset all colors and styles
pub const reset = esc <> "0m"

// Foreground colors
pub const black = esc <> "30m"
pub const red = esc <> "31m"
pub const green = esc <> "32m"
pub const yellow = esc <> "33m"
pub const blue = esc <> "34m"
pub const magenta = esc <> "35m"
pub const cyan = esc <> "36m"
pub const white = esc <> "37m"

// Bright foreground colors
pub const bright_black = esc <> "90m"
pub const bright_red = esc <> "91m"
pub const bright_green = esc <> "92m"
pub const bright_yellow = esc <> "93m"
pub const bright_blue = esc <> "94m"
pub const bright_magenta = esc <> "95m"
pub const bright_cyan = esc <> "96m"
pub const bright_white = esc <> "97m"

// Background colors
pub const bg_black = esc <> "40m"
pub const bg_red = esc <> "41m"
pub const bg_green = esc <> "42m"
pub const bg_yellow = esc <> "43m"
pub const bg_blue = esc <> "44m"
pub const bg_magenta = esc <> "45m"
pub const bg_cyan = esc <> "46m"
pub const bg_white = esc <> "47m"

// Text styles
pub const bold = esc <> "1m"
pub const dim = esc <> "2m"
pub const italic = esc <> "3m"
pub const underline = esc <> "4m"
pub const blink = esc <> "5m"
pub const reverse = esc <> "7m"
pub const hidden = esc <> "8m"
pub const strikethrough = esc <> "9m"

// ============================================================================
// COLOR CONFIGURATION
// ============================================================================

/// Color configuration for terminal output
pub type ColorConfig {
  ColorConfig(
    /// Enable/disable colors
    enabled: Bool,
    /// Force color output even if not a TTY
    force: Bool,
  )
}

/// Default color configuration (auto-detect TTY)
pub const default_config = ColorConfig(enabled: True, force: False)

/// No color configuration (plain text output)
pub const no_color = ColorConfig(enabled: False, force: False)

/// Check if colors should be used
pub fn should_use_colors(config: ColorConfig) -> Bool {
  config.enabled || config.force
}

// ============================================================================
// COLORIZED OUTPUT HELPERS
// ============================================================================

/// Apply a color/style to text if colors are enabled
pub fn colorize(text: String, color: String, config: ColorConfig) -> String {
  case should_use_colors(config) {
    True -> color <> text <> reset
    False -> text
  }
}

/// Apply bold style if colors are enabled
pub fn colorize_bold(text: String, config: ColorConfig) -> String {
  colorize(text, bold, config)
}

/// Apply red color if colors are enabled
pub fn colorize_red(text: String, config: ColorConfig) -> String {
  colorize(text, red, config)
}

/// Apply bright red color if colors are enabled
pub fn colorize_bright_red(text: String, config: ColorConfig) -> String {
  colorize(text, bright_red, config)
}

/// Apply green color if colors are enabled
pub fn colorize_green(text: String, config: ColorConfig) -> String {
  colorize(text, green, config)
}

/// Apply yellow color if colors are enabled
pub fn colorize_yellow(text: String, config: ColorConfig) -> String {
  colorize(text, yellow, config)
}

/// Apply blue color if colors are enabled
pub fn colorize_blue(text: String, config: ColorConfig) -> String {
  colorize(text, blue, config)
}

/// Apply cyan color if colors are enabled
pub fn colorize_cyan(text: String, config: ColorConfig) -> String {
  colorize(text, cyan, config)
}

/// Apply white color if colors are enabled
pub fn colorize_white(text: String, config: ColorConfig) -> String {
  colorize(text, white, config)
}

/// Apply dim style if colors are enabled
pub fn colorize_dim(text: String, config: ColorConfig) -> String {
  colorize(text, dim, config)
}

/// Apply underline style if colors are enabled
pub fn colorize_underline(text: String, config: ColorConfig) -> String {
  colorize(text, underline, config)
}

// ============================================================================
// ERROR-SPECIFIC COLOR HELPERS
// ============================================================================

/// Colorize error header (bright red + bold)
pub fn colorize_error_header(text: String, config: ColorConfig) -> String {
  colorize(text, bright_red <> bold, config)
}

/// Colorize warning header (bright yellow + bold)
pub fn colorize_warning_header(text: String, config: ColorConfig) -> String {
  colorize(text, bright_yellow <> bold, config)
}

/// Colorize info header (bright blue + bold)
pub fn colorize_info_header(text: String, config: ColorConfig) -> String {
  colorize(text, bright_blue <> bold, config)
}

/// Colorize tip/explanation (cyan)
pub fn colorize_tip(text: String, config: ColorConfig) -> String {
  colorize(text, cyan, config)
}

/// Colorize note (dim white)
pub fn colorize_note(text: String, config: ColorConfig) -> String {
  colorize(text, bright_black, config)
}

/// Colorize help/suggestion (green)
pub fn colorize_help(text: String, config: ColorConfig) -> String {
  colorize(text, green, config)
}

/// Colorize file path (white)
pub fn colorize_path(text: String, config: ColorConfig) -> String {
  colorize(text, white, config)
}

/// Colorize line number (cyan)
pub fn colorize_line_num(text: String, config: ColorConfig) -> String {
  colorize(text, cyan, config)
}

/// Colorize source code (white)
pub fn colorize_source(text: String, config: ColorConfig) -> String {
  colorize(text, white, config)
}

/// Colorize pointer/caret (bright red)
pub fn colorize_pointer(text: String, config: ColorConfig) -> String {
  colorize(text, bright_red, config)
}

// ============================================================================
// STRIP ANSI CODES
// ============================================================================

/// Remove all ANSI escape codes from a string
pub fn strip_ansi_codes(text: String) -> String {
  // Simple approach: remove common ANSI sequences
  let escape = "\u{1b}["
  text
  |> string.replace(escape <> "0m", "")
  |> string.replace(escape <> "1m", "")
  |> string.replace(escape <> "2m", "")
  |> string.replace(escape <> "3m", "")
  |> string.replace(escape <> "4m", "")
  |> string.replace(escape <> "30m", "")
  |> string.replace(escape <> "31m", "")
  |> string.replace(escape <> "32m", "")
  |> string.replace(escape <> "33m", "")
  |> string.replace(escape <> "34m", "")
  |> string.replace(escape <> "35m", "")
  |> string.replace(escape <> "36m", "")
  |> string.replace(escape <> "37m", "")
  |> string.replace(escape <> "90m", "")
  |> string.replace(escape <> "91m", "")
  |> string.replace(escape <> "92m", "")
  |> string.replace(escape <> "93m", "")
  |> string.replace(escape <> "94m", "")
  |> string.replace(escape <> "95m", "")
  |> string.replace(escape <> "96m", "")
  |> string.replace(escape <> "97m", "")
  |> string.replace(escape <> "40m", "")
  |> string.replace(escape <> "41m", "")
  |> string.replace(escape <> "42m", "")
  |> string.replace(escape <> "43m", "")
  |> string.replace(escape <> "44m", "")
  |> string.replace(escape <> "45m", "")
  |> string.replace(escape <> "46m", "")
  |> string.replace(escape <> "47m", "")
}
