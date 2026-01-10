//! # rource-core
//!
//! Core visualization engine for the Rource project.
//!
//! This crate contains:
//! - Entity management (users, files, directories)
//! - Scene graph
//! - Physics simulation
//! - Animation system
//! - Camera system
//!
//! ## Architecture
//!
//! The core engine is designed around an ECS-like architecture where:
//! - Entities are identified by typed IDs
//! - Components store data
//! - Systems process the data each frame

// Lints are configured in workspace Cargo.toml

pub mod entity;

pub use entity::{ActionId, DirId, EntityId, FileId, UserId};
