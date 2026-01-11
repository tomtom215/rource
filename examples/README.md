# Rource Examples

This directory contains example configurations for common use cases.

## Configuration Files

| File | Description |
|------|-------------|
| `basic.toml` | Simple configuration with common options |
| `video-export.toml` | Optimized for batch video export |
| `large-repo.toml` | Performance settings for large repositories |
| `presentation.toml` | High-quality settings for presentations |
| `minimal.toml` | Minimal UI for clean output |
| `rust-project.toml` | Settings for Rust projects |
| `web-project.toml` | Settings for web projects (Node.js/TypeScript) |

## Usage

```bash
# Use a config file
rource --config examples/basic.toml /path/to/repo

# Generate your own config
rource --sample-config > my-config.toml
```

## Shell Scripts

| File | Description |
|------|-------------|
| `export-video.sh` | Export repository to MP4 video |
| `quick-preview.sh` | Fast preview with reduced quality |

## Custom Log Examples

| File | Description |
|------|-------------|
| `sample-custom.log` | Example custom log format |
