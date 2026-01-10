//! # rource-core
//!
//! Core visualization engine for the Rource project.
//!
//! This crate contains:
//! - Entity management (users, files, directories)
//! - Scene graph
//! - Physics simulation (force-directed layout)
//! - Animation system (tweening, splines)
//! - Camera system (pan, zoom, tracking)
//!
//! ## Architecture
//!
//! The core engine is designed around an ECS-like architecture where:
//! - Entities are identified by typed IDs
//! - Components store data
//! - Systems process the data each frame
//!
//! ## Example
//!
//! ```
//! use rource_core::scene::{Scene, ActionType};
//! use std::path::PathBuf;
//!
//! // Create a new scene
//! let mut scene = Scene::new();
//!
//! // Apply a commit
//! scene.apply_commit("Alice", &[
//!     (PathBuf::from("src/main.rs"), ActionType::Create),
//!     (PathBuf::from("src/lib.rs"), ActionType::Modify),
//! ]);
//!
//! // Update the scene
//! scene.update(0.016); // 60 FPS
//! ```

// Lints are configured in workspace Cargo.toml

pub mod animation;
pub mod camera;
pub mod entity;
pub mod physics;
pub mod scene;

pub use animation::{ease, interpolate, lerp, CatmullRomSpline, Easing, Tween};
pub use camera::{Camera, CameraMode, CameraTracker};
pub use entity::{ActionId, DirId, EntityId, FileId, Generation, IdAllocator, RawEntityId, UserId};
pub use physics::{ForceConfig, ForceSimulation, QuadTree, SimulationStats};
pub use scene::Scene;
