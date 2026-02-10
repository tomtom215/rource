// SPDX-License-Identifier: GPL-3.0-or-later
// Copyright (C) 2026 Tom F <https://github.com/tomtom215>

//! Developer collaboration network analysis.
//!
//! Builds an implicit developer collaboration graph from shared file
//! modifications and computes centrality metrics to identify key connector
//! developers, isolated silos, and structural holes.
//!
//! # Research Basis
//!
//! Begel et al. (2023) "Modeling the Centrality of Developer Output with Software
//! Supply Chains" (ESEC/FSE 2023, Industry Track): centrality explains 30%+ of
//! developer impact variance.
//!
//! Meneely & Williams (2011) "Socio-Technical Developer Networks" (MSR 2011):
//! network analysis predicts security vulnerabilities.
//!
//! Wolf et al. (2009) "Predicting Build Failures Using Social Network Analysis on
//! Developer Communication" (ICSE 2009): network metrics predict build failures.
//!
//! # Algorithm
//!
//! 1. Build developer adjacency from shared files: weight\[d₁\]\[d₂\] = shared file count
//! 2. Degree centrality: number of unique collaborators
//! 3. Clustering coefficient: how connected a developer's neighbors are
//! 4. Connected components via BFS for silo detection
//! 5. Network density = 2 × edges / (V × (V − 1))
//!
//! # Complexity
//!
//! - Building adjacency: O(F × d²) where d = avg developers per file
//! - Degree + clustering: O(V + E)
//! - Connected components: O(V + E) via BFS

use rustc_hash::{FxHashMap, FxHashSet};

/// Maximum number of developers for betweenness centrality computation.
/// Beyond this, betweenness is skipped (set to 0.0) since it's O(V×E).
const MAX_DEVS_FOR_BETWEENNESS: usize = 100;

/// A developer node in the collaboration network.
#[derive(Debug, Clone)]
pub struct DeveloperNode {
    /// Developer name.
    pub author: String,
    /// Number of unique collaborator connections (degree centrality).
    pub degree: u32,
    /// Betweenness centrality: fraction of shortest paths through this developer.
    pub betweenness: f64,
    /// Clustering coefficient: how connected this developer's neighbors are.
    pub clustering_coefficient: f64,
    /// Total shared files across all connections.
    pub shared_files_total: u32,
    /// Connected component ID (for silo detection).
    pub component_id: u32,
}

/// Complete developer network report.
#[derive(Debug, Clone)]
pub struct NetworkReport {
    /// Developer nodes sorted by degree descending.
    pub developers: Vec<DeveloperNode>,
    /// Overall network density in \[0, 1\].
    pub network_density: f64,
    /// Number of connected components (isolated groups).
    pub connected_components: u32,
    /// Size of the largest connected component.
    pub largest_component_size: u32,
    /// Total collaboration edges.
    pub total_edges: u32,
    /// Mean connections per developer.
    pub avg_degree: f64,
}

/// Computes the developer collaboration network from file-author data.
///
/// # Arguments
///
/// * `file_authors` - Map of `file_path` → (`author` → change count)
#[must_use]
#[allow(clippy::implicit_hasher)]
pub fn compute_network(file_authors: &FxHashMap<String, FxHashMap<String, u32>>) -> NetworkReport {
    if file_authors.is_empty() {
        return NetworkReport {
            developers: Vec::new(),
            network_density: 0.0,
            connected_components: 0,
            largest_component_size: 0,
            total_edges: 0,
            avg_degree: 0.0,
        };
    }

    // Build adjacency: dev → (neighbor → shared file count)
    let mut adjacency: FxHashMap<String, FxHashMap<String, u32>> = FxHashMap::default();
    let mut all_devs: FxHashSet<String> = FxHashSet::default();

    for authors in file_authors.values() {
        let dev_list: Vec<&str> = authors.keys().map(String::as_str).collect();
        for &dev in &dev_list {
            all_devs.insert(dev.to_string());
        }
        for i in 0..dev_list.len() {
            for j in (i + 1)..dev_list.len() {
                *adjacency
                    .entry(dev_list[i].to_string())
                    .or_default()
                    .entry(dev_list[j].to_string())
                    .or_insert(0) += 1;
                *adjacency
                    .entry(dev_list[j].to_string())
                    .or_default()
                    .entry(dev_list[i].to_string())
                    .or_insert(0) += 1;
            }
        }
    }

    let v = all_devs.len();
    let total_edges = adjacency
        .values()
        .map(|neighbors| neighbors.len() as u32)
        .sum::<u32>()
        / 2; // each edge counted twice

    // Assign developer indices for component detection
    let dev_list: Vec<String> = all_devs.into_iter().collect();
    let dev_idx: FxHashMap<&str, usize> = dev_list
        .iter()
        .enumerate()
        .map(|(i, d)| (d.as_str(), i))
        .collect();

    // Connected components via BFS
    let components = find_components(&dev_list, &adjacency, &dev_idx);
    let connected_components = *components.values().max().unwrap_or(&0) + 1;
    let mut component_sizes: FxHashMap<u32, u32> = FxHashMap::default();
    for &c in components.values() {
        *component_sizes.entry(c).or_insert(0) += 1;
    }
    let largest_component_size = component_sizes.values().copied().max().unwrap_or(0);

    // Compute betweenness (simplified, only for small networks)
    let betweenness = if (3..=MAX_DEVS_FOR_BETWEENNESS).contains(&v) {
        compute_betweenness(&dev_list, &adjacency, &dev_idx)
    } else {
        FxHashMap::default()
    };

    // Build developer nodes
    let mut developers: Vec<DeveloperNode> = dev_list
        .iter()
        .map(|dev| {
            let neighbors = adjacency.get(dev.as_str());
            let degree = neighbors.map_or(0, |n| n.len() as u32);
            let shared_files_total: u32 = neighbors.map_or(0, |n| n.values().sum());
            let clustering = compute_clustering(dev, &adjacency);
            let component_id = components.get(dev.as_str()).copied().unwrap_or(0);
            let betw = betweenness.get(dev.as_str()).copied().unwrap_or(0.0);

            DeveloperNode {
                author: dev.clone(),
                degree,
                betweenness: betw,
                clustering_coefficient: clustering,
                shared_files_total,
                component_id,
            }
        })
        .collect();

    developers.sort_by(|a, b| b.degree.cmp(&a.degree));

    let network_density = if v >= 2 {
        2.0 * f64::from(total_edges) / (v as f64 * (v as f64 - 1.0))
    } else {
        0.0
    };

    let avg_degree = if v > 0 {
        2.0 * f64::from(total_edges) / v as f64
    } else {
        0.0
    };

    NetworkReport {
        developers,
        network_density,
        connected_components,
        largest_component_size,
        total_edges,
        avg_degree,
    }
}

/// Finds connected components using BFS.
fn find_components(
    dev_list: &[String],
    adjacency: &FxHashMap<String, FxHashMap<String, u32>>,
    dev_idx: &FxHashMap<&str, usize>,
) -> FxHashMap<String, u32> {
    let mut visited = vec![false; dev_list.len()];
    let mut components: FxHashMap<String, u32> = FxHashMap::default();
    let mut component_id: u32 = 0;

    for (i, dev) in dev_list.iter().enumerate() {
        if visited[i] {
            continue;
        }

        // BFS
        let mut queue = std::collections::VecDeque::new();
        queue.push_back(dev.as_str());
        visited[i] = true;

        while let Some(current) = queue.pop_front() {
            components.insert(current.to_string(), component_id);
            if let Some(neighbors) = adjacency.get(current) {
                for neighbor in neighbors.keys() {
                    if let Some(&idx) = dev_idx.get(neighbor.as_str()) {
                        if !visited[idx] {
                            visited[idx] = true;
                            queue.push_back(neighbor.as_str());
                        }
                    }
                }
            }
        }

        component_id += 1;
    }

    components
}

/// Computes clustering coefficient for a developer.
///
/// Clustering = edges among neighbors / possible edges among neighbors.
fn compute_clustering(dev: &str, adjacency: &FxHashMap<String, FxHashMap<String, u32>>) -> f64 {
    let neighbors: Vec<&str> = adjacency
        .get(dev)
        .map_or_else(Vec::new, |n| n.keys().map(String::as_str).collect());

    let k = neighbors.len();
    if k < 2 {
        return 0.0;
    }

    let neighbor_set: FxHashSet<&str> = neighbors.iter().copied().collect();
    let mut edges_among_neighbors: u32 = 0;

    for &n1 in &neighbors {
        if let Some(n1_neighbors) = adjacency.get(n1) {
            for n2 in n1_neighbors.keys() {
                if neighbor_set.contains(n2.as_str()) {
                    edges_among_neighbors += 1;
                }
            }
        }
    }

    // Each edge counted twice (n1→n2 and n2→n1)
    let actual_edges = edges_among_neighbors / 2;
    let possible_edges = (k * (k - 1)) / 2;

    f64::from(actual_edges) / possible_edges as f64
}

/// Computes betweenness centrality using BFS from each node.
fn compute_betweenness(
    dev_list: &[String],
    adjacency: &FxHashMap<String, FxHashMap<String, u32>>,
    dev_idx: &FxHashMap<&str, usize>,
) -> FxHashMap<String, f64> {
    let v = dev_list.len();
    let mut betweenness: Vec<f64> = vec![0.0; v];

    for s in 0..v {
        // BFS-based shortest path counting (Brandes' algorithm)
        let mut stack: Vec<usize> = Vec::new();
        let mut predecessors: Vec<Vec<usize>> = vec![Vec::new(); v];
        let mut sigma = vec![0.0f64; v]; // number of shortest paths
        sigma[s] = 1.0;
        let mut dist = vec![-1i64; v];
        dist[s] = 0;

        let mut queue = std::collections::VecDeque::new();
        queue.push_back(s);

        while let Some(current) = queue.pop_front() {
            stack.push(current);
            if let Some(neighbors) = adjacency.get(dev_list[current].as_str()) {
                for neighbor_name in neighbors.keys() {
                    if let Some(&w) = dev_idx.get(neighbor_name.as_str()) {
                        if dist[w] < 0 {
                            dist[w] = dist[current] + 1;
                            queue.push_back(w);
                        }
                        if dist[w] == dist[current] + 1 {
                            sigma[w] += sigma[current];
                            predecessors[w].push(current);
                        }
                    }
                }
            }
        }

        // Accumulate dependencies
        let mut delta = vec![0.0f64; v];
        while let Some(w) = stack.pop() {
            for &pred in &predecessors[w] {
                delta[pred] += (sigma[pred] / sigma[w]) * (1.0 + delta[w]);
            }
            if w != s {
                betweenness[w] += delta[w];
            }
        }
    }

    // Normalize for undirected graph: divide by 2
    let norm = if v >= 3 {
        ((v - 1) * (v - 2)) as f64
    } else {
        1.0
    };

    dev_list
        .iter()
        .enumerate()
        .map(|(i, dev)| (dev.clone(), betweenness[i] / norm))
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_file_authors(entries: &[(&str, &[&str])]) -> FxHashMap<String, FxHashMap<String, u32>> {
        entries
            .iter()
            .map(|(path, authors)| {
                let author_map: FxHashMap<String, u32> =
                    authors.iter().map(|a| (a.to_string(), 1)).collect();
                (path.to_string(), author_map)
            })
            .collect()
    }

    #[test]
    fn test_isolated_developers() {
        // Each dev works on a different file → no edges, components = N
        let fa = make_file_authors(&[
            ("a.rs", &["Alice"]),
            ("b.rs", &["Bob"]),
            ("c.rs", &["Carol"]),
        ]);
        let report = compute_network(&fa);
        assert_eq!(report.developers.len(), 3);
        assert_eq!(report.total_edges, 0);
        assert_eq!(report.connected_components, 3);
        assert_eq!(report.largest_component_size, 1);
        assert!(
            report.network_density.abs() < f64::EPSILON,
            "density={}, expected=0.0",
            report.network_density
        );
        for dev in &report.developers {
            assert_eq!(dev.degree, 0);
        }
    }

    #[test]
    fn test_fully_connected() {
        // All devs share same file → complete graph
        let fa = make_file_authors(&[("shared.rs", &["Alice", "Bob", "Carol"])]);
        let report = compute_network(&fa);
        assert_eq!(report.total_edges, 3); // C(3,2) = 3
        assert_eq!(report.connected_components, 1);
        assert!(
            (report.network_density - 1.0).abs() < 1e-10,
            "density={}, expected=1.0",
            report.network_density
        );
        for dev in &report.developers {
            assert_eq!(dev.degree, 2);
        }
    }

    #[test]
    fn test_two_components() {
        // Two groups with no shared files → 2 components
        let fa = make_file_authors(&[
            ("team1.rs", &["Alice", "Bob"]),
            ("team2.rs", &["Carol", "Dave"]),
        ]);
        let report = compute_network(&fa);
        assert_eq!(report.connected_components, 2);
        assert_eq!(report.total_edges, 2);
        assert_eq!(report.largest_component_size, 2);
    }

    #[test]
    fn test_degree_calculation() {
        // Alice shares files with Bob and Carol; Bob only with Alice
        let fa = make_file_authors(&[("ab.rs", &["Alice", "Bob"]), ("ac.rs", &["Alice", "Carol"])]);
        let report = compute_network(&fa);
        let alice = report
            .developers
            .iter()
            .find(|d| d.author == "Alice")
            .unwrap();
        assert_eq!(alice.degree, 2, "Alice should have degree 2");
        let bob = report
            .developers
            .iter()
            .find(|d| d.author == "Bob")
            .unwrap();
        assert_eq!(bob.degree, 1, "Bob should have degree 1");
    }

    #[test]
    fn test_clustering_triangle() {
        // 3 devs all connected → clustering = 1.0 each
        let fa = make_file_authors(&[("shared.rs", &["Alice", "Bob", "Carol"])]);
        let report = compute_network(&fa);
        for dev in &report.developers {
            assert!(
                (dev.clustering_coefficient - 1.0).abs() < 1e-10,
                "dev={}, clustering={}, expected=1.0",
                dev.author,
                dev.clustering_coefficient
            );
        }
    }

    #[test]
    fn test_clustering_star() {
        // Central dev (Alice) with 3 unconnected neighbors
        let fa = make_file_authors(&[
            ("ab.rs", &["Alice", "Bob"]),
            ("ac.rs", &["Alice", "Carol"]),
            ("ad.rs", &["Alice", "Dave"]),
        ]);
        let report = compute_network(&fa);
        let alice = report
            .developers
            .iter()
            .find(|d| d.author == "Alice")
            .unwrap();
        // Alice's neighbors (Bob, Carol, Dave) have no edges between them
        assert!(
            alice.clustering_coefficient.abs() < f64::EPSILON,
            "star center clustering={}, expected=0.0",
            alice.clustering_coefficient
        );
    }

    #[test]
    fn test_network_density() {
        // 4 devs, 3 edges → density = 2*3/(4*3) = 0.5
        let fa = make_file_authors(&[
            ("ab.rs", &["Alice", "Bob"]),
            ("bc.rs", &["Bob", "Carol"]),
            ("cd.rs", &["Carol", "Dave"]),
        ]);
        let report = compute_network(&fa);
        assert_eq!(report.total_edges, 3);
        let expected = 2.0 * 3.0 / (4.0 * 3.0);
        assert!(
            (report.network_density - expected).abs() < 1e-10,
            "density={}, expected={}",
            report.network_density,
            expected
        );
    }

    #[test]
    fn test_empty_network() {
        let report = compute_network(&FxHashMap::default());
        assert!(report.developers.is_empty());
        assert_eq!(report.connected_components, 0);
        assert_eq!(report.total_edges, 0);
    }

    #[test]
    fn test_single_developer() {
        let fa = make_file_authors(&[("a.rs", &["Alice"])]);
        let report = compute_network(&fa);
        assert_eq!(report.developers.len(), 1);
        assert_eq!(report.developers[0].degree, 0);
        assert_eq!(report.connected_components, 1);
        assert!(
            report.network_density.abs() < f64::EPSILON,
            "single dev → density=0"
        );
    }

    #[test]
    fn test_avg_degree() {
        // 3 devs in a triangle → 3 edges → avg degree = 2*3/3 = 2.0
        let fa = make_file_authors(&[("shared.rs", &["Alice", "Bob", "Carol"])]);
        let report = compute_network(&fa);
        assert!(
            (report.avg_degree - 2.0).abs() < 1e-10,
            "avg_degree={}, expected=2.0",
            report.avg_degree
        );
    }
}
