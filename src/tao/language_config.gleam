// Tao Language Configuration
// Defines language-specific settings.

/// Tao language configuration
pub type Config {
  Config(
    name: String,
    version: String,
    strict_mode: Bool,
  )
}

/// Default Tao configuration
pub fn default_config() -> Config {
  Config(
    name: "Tao",
    version: "0.1.0",
    strict_mode: True,
  )
}
