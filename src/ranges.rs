//
// Copyright 2025 Hans W. Uhlig. All Rights Reserved.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//

use std::cmp::{max, min};
use std::ops::Range;

/// A `RangeMap` tracks a set of non-overlapping ranges, each with an associated reference count.
///
/// Internally implemented as a self-balancing red-black tree, the `RangeMap` allows
/// incrementing and decrementing reference counts over ranges, automatically splitting and
/// merging ranges as necessary to preserve disjoint, minimal representation.
///
/// # Examples
///
/// ```notest
/// use rangelock::RangeMap;
///
/// let mut map = RangeMap::new();
///
/// map.increment(10..20);
/// map.increment(15..25);
/// map.decrement(16..18);
///
/// // Now the internal state has refcounts adjusted per segment.
/// ```
#[derive(Default)]
pub struct RangeMap {
    root: Link,
}

impl RangeMap {
    /// Creates an empty `RangeMap`.
    ///
    /// # Examples
    /// ```notest
    /// use rangelock::RangeMap;
    ///
    /// let map = RangeMap::new();
    /// ```
    pub fn new() -> Self {
        RangeMap { root: None }
    }

    /// Increments the reference count for a given range.
    ///
    /// If the inserted range overlaps with existing ranges, only the overlapping sections
    /// are incremented accordingly. Disjoint ranges are added as new segments with a count of 1.
    ///
    /// The tree automatically splits and merges ranges to maintain non-overlapping intervals.
    ///
    /// # Arguments
    ///
    /// * `range` - A half-open interval `[start, end)` to increment.
    ///
    /// # Examples
    ///
    /// ```notest
    /// use rangelock::RangeMap;
    ///
    /// let mut map = RangeMap::new();
    /// map.increment(10..20);
    /// map.increment(15..25);
    /// // Results in: [10..15] x1, [15..20] x2, [20..25] x1
    /// ```
    pub fn increment(&mut self, range: Range<usize>) {
        // Ignore zero-length ranges
        if range.start >= range.end {
            return;
        }

        self.root = Self::insert(self.root.take(), range, 1);
        if let Some(ref mut root) = self.root {
            root.color = Color::Black;
        }
    }

    /// Decrements the reference count for a given range.
    ///
    /// If a range's count reaches 0, it is removed from the map.
    /// The function has no effect on ranges outside the current coverage.
    ///
    /// # Arguments
    ///
    /// * `range` - A half-open interval `[start, end)` to decrement.
    ///
    /// # Examples
    ///
    /// ```notest
    /// use rangelock::RangeMap;
    ///
    /// let mut map = RangeMap::new();
    /// map.increment(10..20);
    /// map.increment(15..25);
    /// map.decrement(16..18);
    /// // [16..18] drops from 2 to 1; rest are unaffected
    /// ```
    pub fn decrement(&mut self, range: Range<usize>) {
        // Ignore zero-length ranges
        if range.start >= range.end {
            return;
        }

        self.root = Self::insert(self.root.take(), range, -1);
        if let Some(ref mut root) = self.root {
            root.color = Color::Black;
        }
    }

    /// Inserts a new range with the given reference count directly into the tree.
    ///
    /// This function does not merge or split existing ranges.
    /// It assumes the range does not overlap with any other range already in the tree,
    /// so it should only be called after handling overlaps (e.g., via `increment`).
    ///
    /// If a node already exists with the exact same range, it replaces its refcount.
    ///
    /// # Arguments
    ///
    /// * `range` - The range to insert (must not overlap existing ranges).
    /// * `refcount` - The reference count to associate with this range.
    ///
    /// # Safety
    ///
    /// - Caller must ensure the tree remains balanced after insertion.
    /// - No range overlap or duplication is allowed.
    fn insert(h: Link, range: Range<usize>, delta: i32) -> Link {
        if h.is_none() {
            // If no node exists, create a new one with the current delta
            return if delta > 0 {
                Some(Node::new(range, delta as usize))
            } else {
                None
            };
        }

        let mut node = h.unwrap();

        // Handle non-overlapping ranges
        if range.end <= node.range.start {
            node.left = Self::insert(node.left.take(), range, delta);
            // Merge adjacent ranges in the left subtree
            node.left = Self::merge(node.left.take(), node.left.take());
        } else if range.start >= node.range.end {
            node.right = Self::insert(node.right.take(), range, delta);
            // Merge adjacent ranges in the right subtree
            node.right = Self::merge(node.right.take(), node.right.take());
        } else {
            // Handle overlapping ranges by splitting and adjusting
            let overlap_start = max(range.start, node.range.start);
            let overlap_end = min(range.end, node.range.end);

            let left_range = node.range.start..overlap_start;
            let right_range = overlap_end..node.range.end;

            if left_range.start < left_range.end {
                node.left =
                    Self::insert(node.left.take(), left_range.clone(), node.refcount as i32);
            }

            if right_range.start < right_range.end {
                node.right =
                    Self::insert(node.right.take(), right_range.clone(), node.refcount as i32);
            }

            let new_count = node.refcount as i32 + delta;
            if new_count > 0 {
                node.range = overlap_start..overlap_end;
                node.refcount = new_count as usize;
            } else {
                // If the range count becomes zero, remove this node and merge its children
                return Self::merge(node.left.take(), node.right.take());
            }

            // Handle the remaining ranges in the input range
            if range.start < overlap_start {
                node.left = Self::insert(node.left.take(), range.start..overlap_start, delta);
            }
            if range.end > overlap_end {
                node.right = Self::insert(node.right.take(), overlap_end..range.end, delta);
            }
        }

        // Merge adjacent ranges in the current node context if they are compatible
        if let Some(left) = node.left.take() {
            if left.range.end == node.range.start && left.refcount == node.refcount {
                // Merge left child into the current node
                node.range.start = left.range.start;
                node.left = left.left;
            } else {
                node.left = Some(left);
            }
        }

        if let Some(right) = node.right.take() {
            if node.range.end == right.range.start && node.refcount == right.refcount {
                // Merge right child into the current node
                node.range.end = right.range.end;
                node.right = right.right;
            } else {
                node.right = Some(right);
            }
        }

        // Red-black balancing
        if Node::is_red(&node.right) && !Node::is_red(&node.left) {
            node = Node::rotate_left(node);
        }
        if Node::is_red(&node.left) && Node::is_red(&node.left.as_ref().unwrap().left) {
            node = Node::rotate_right(node);
        }
        if Node::is_red(&node.left) && Node::is_red(&node.right) {
            Node::flip_colors(&mut node);
        }

        Some(node)
    }

    /// Merges adjacent nodes with identical reference counts.
    ///
    /// After a sequence of operations (e.g., `decrement`, `increment`), it's possible
    /// that the tree contains adjacent nodes like `[10..20] x1` and `[20..30] x1`.
    /// This function detects such pairs and merges them into a single `[10..30] x1`.
    ///
    /// This helps keep the tree compact and avoids unnecessary fragmentation.
    ///
    /// # Usage
    ///
    /// Typically called after `increment` or `decrement` to clean up the tree structure.
    fn merge(left: Link, right: Link) -> Link {
        // Base cases: if either side is None, return the other
        if left.is_none() {
            return right;
        }
        if right.is_none() {
            return left;
        }

        let mut left_node = left.unwrap();
        let right_node = right.unwrap();

        // If ranges are adjacent and have the same refcount, merge them
        if left_node.range.end == right_node.range.start
            && left_node.refcount == right_node.refcount
        {
            left_node.range.end = right_node.range.end;
            left_node.right = right_node.right;
            return Some(left_node);
        }

        // Otherwise, link the two subtrees while maintaining order
        left_node.right = Self::merge(left_node.right.take(), Some(right_node));
        Some(left_node)
    }

    /// Checks if a range is fully contained within the tracked ranges.
    ///
    /// A range is considered "contained" only if every point in the input range is covered
    /// by one or more ranges in the map. This is stricter than `overlaps()` as it requires
    /// complete coverage.
    ///
    /// # Arguments
    ///
    /// * `range` - The range to check for containment
    ///
    /// # Returns
    ///
    /// * `true` - If the entire input range is contained within tracked ranges
    /// * `false` - If any part of the input range is not contained, or if the range is invalid
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rangelock::RangeMap;
    ///
    /// let mut map = RangeMap::new();
    /// map.increment(10..30);
    ///
    /// assert!(map.contains(15..25));     // Fully contained
    /// assert!(!map.contains(5..15));     // Partially outside
    /// assert!(!map.contains(0..5));      // Completely outside
    /// assert!(!map.contains(10..10));     // Empty range within bounds
    /// ```
    ///
    /// # Edge Cases
    ///
    /// * Empty ranges (where start == end) return true if they fall within a tracked range
    /// * Invalid ranges (where start > end) always return false
    /// * Zero-length ranges at the boundary of a tracked range return false

    pub fn contains(&self, range: Range<usize>) -> bool {
        // Handle case where start >= end (empty range)
        if range.start >= range.end {
            return false;
        }

        Self::contains_recursive(&self.root, range)
    }

    /// Recursive helper for contains check.
    fn contains_recursive(node: &Link, range: Range<usize>) -> bool {
        if let Some(n) = node {
            // Check overlap conditions
            if range.start >= n.range.end {
                // Go right
                return Self::contains_recursive(&n.right, range);
            } else if range.end <= n.range.start {
                // Go left
                return Self::contains_recursive(&n.left, range);
            } else {
                // Overlap exists; verify it is fully contained
                let contains_left = range.start >= n.range.start;
                let contains_right = range.end <= n.range.end;

                if contains_left && contains_right && n.refcount > 0 {
                    return true;
                }

                // Check any remaining uncovered range segments
                let left_result = if range.start < n.range.start {
                    Self::contains_recursive(&n.left, range.start..n.range.start)
                } else {
                    true
                };

                let right_result = if range.end > n.range.end {
                    Self::contains_recursive(&n.right, n.range.end..range.end)
                } else {
                    true
                };

                return left_result && right_result;
            }
        }

        false
    }

    /// Checks if a range overlaps with any tracked ranges.
    ///
    /// A range is considered "overlapping" if there exists any point that is present in both
    /// the input range and any tracked range. This is less strict than `contains()` as it
    /// only requires partial intersection.
    ///
    /// # Arguments
    ///
    /// * `range` - The range to check for overlap
    ///
    /// # Returns
    ///
    /// * `true` - If the input range overlaps with any tracked range
    /// * `false` - If there is no overlap, or if the range is invalid
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rangelock::RangeMap;
    ///
    /// let mut map = RangeMap::new();
    /// map.increment(10..30);
    ///
    /// assert!(map.overlaps(25..35));     // Partial overlap
    /// assert!(map.overlaps(15..25));     // Contained overlap
    /// assert!(map.overlaps(0..40));      // Containing overlap
    /// assert!(!map.overlaps(0..10));     // No overlap
    /// assert!(!map.overlaps(30..40));    // Adjacent, no overlap
    /// ```
    ///
    /// # Edge Cases
    ///
    /// * Empty ranges (where start == end) always return false
    /// * Invalid ranges (where start > end) always return false
    /// * Adjacent ranges (sharing only an endpoint) do not overlap
    /// * Multiple overlapping tracked ranges are treated as a single range

    pub fn overlaps(&self, range: Range<usize>) -> bool {
        if range.start >= range.end {
            return false;
        }

        let mut current = &self.root;
        while let Some(node) = current {
            if range.end <= node.range.start {
                current = &node.left;
            } else if range.start >= node.range.end {
                current = &node.right;
            } else {
                return true;
            }
        }
        false
    }
}

impl std::fmt::Debug for RangeMap {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        /// Prints a visual tree structure of the internal range map.
        ///
        /// Intended for debugging and visualization. The output includes range boundaries,
        /// refcounts, and node color in the red-black tree.
        fn recurse(node: &Link, depth: usize, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            if let Some(n) = node {
                recurse(&n.left, depth + 1, f)?;
                println!(
                    "{:indent$}[{}..{}) x{} ({:?})",
                    "",
                    n.range.start,
                    n.range.end,
                    n.refcount,
                    n.color,
                    indent = depth * 2
                );
                recurse(&n.right, depth + 1, f)?;
            }
            Ok(())
        }
        recurse(&self.root, 0, f)
    }
}

/// An in-order iterator over the stored ranges and their reference counts.
pub struct RangeMapIter<'a> {
    stack: Vec<&'a Node>,
    current: Option<&'a Node>,
}

impl<'a> Iterator for RangeMapIter<'a> {
    type Item = (Range<usize>, usize);

    fn next(&mut self) -> Option<Self::Item> {
        let mut curr = self.current;
        while let Some(node) = curr {
            self.stack.push(node);
            curr = node.left.as_deref();
        }
        let node = self.stack.pop()?;
        self.current = node.right.as_deref();
        Some((node.range.clone(), node.refcount))
    }
}

/// A node in the Red-Black Tree
#[derive(Clone, Debug)]
struct Node {
    range: Range<usize>,
    refcount: usize,
    color: Color,
    left: Link,
    right: Link,
}

type Link = Option<Box<Node>>;

#[derive(Debug, PartialEq, Clone, Copy)]
enum Color {
    Red,
    Black,
}

impl Node {
    fn new(range: Range<usize>, refcount: usize) -> Box<Node> {
        Box::new(Node {
            range,
            refcount,
            color: Color::Red,
            left: None,
            right: None,
        })
    }

    fn is_red(link: &Link) -> bool {
        match link {
            Some(node) => node.color == Color::Red,
            None => false,
        }
    }

    fn rotate_left(mut h: Box<Node>) -> Box<Node> {
        let mut x = h.right.take().unwrap();
        h.right = x.left.take();
        x.left = Some(h);
        x.color = x.left.as_ref().unwrap().color;
        x.left.as_mut().unwrap().color = Color::Red;
        x
    }

    fn rotate_right(mut h: Box<Node>) -> Box<Node> {
        let mut x = h.left.take().unwrap();
        h.left = x.right.take();
        x.right = Some(h);
        x.color = x.right.as_ref().unwrap().color;
        x.right.as_mut().unwrap().color = Color::Red;
        x
    }

    fn flip_colors(h: &mut Box<Node>) {
        h.color = Color::Red;
        if let Some(ref mut left) = h.left {
            left.color = Color::Black;
        }
        if let Some(ref mut right) = h.right {
            right.color = Color::Black;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn extract_ranges(map: &RangeMap) -> Vec<(usize, usize, usize)> {
        let mut out = vec![];
        fn recurse(node: &Link, out: &mut Vec<(usize, usize, usize)>) {
            if let Some(n) = node {
                recurse(&n.left, out);
                out.push((n.range.start, n.range.end, n.refcount));
                recurse(&n.right, out);
            }
        }
        recurse(&map.root, &mut out);
        out
    }

    #[test]
    fn test_single_insert() {
        let mut map = RangeMap::new();
        map.increment(10..20);
        let ranges = extract_ranges(&map);
        assert_eq!(ranges, vec![(10, 20, 1)]);
    }

    #[test]
    fn test_non_overlapping_inserts() {
        let mut map = RangeMap::new();
        map.increment(10..20);
        map.increment(30..40);
        let ranges = extract_ranges(&map);
        assert_eq!(ranges, vec![(10, 20, 1), (30, 40, 1)]);
    }

    #[test]
    fn test_overlapping_inserts_merge() {
        let mut map = RangeMap::new();
        map.increment(10..20);
        map.increment(15..25);
        let ranges = extract_ranges(&map);
        assert_eq!(ranges, vec![(10, 15, 1), (15, 20, 2), (20, 25, 1)]);
    }

    #[test]
    fn test_multiple_overlapping_levels() {
        let mut map = RangeMap::new();
        map.increment(10..20);
        map.increment(15..25);
        map.increment(18..22);
        let ranges = extract_ranges(&map);
        assert_eq!(
            ranges,
            vec![
                (10, 15, 1),
                (15, 18, 2),
                (18, 20, 3),
                (20, 22, 2),
                (22, 25, 1),
            ]
        );
    }

    #[test]
    fn test_decrement_middle_overlap() {
        let mut map = RangeMap::new();
        map.increment(10..20);
        map.increment(15..25);
        map.decrement(16..18);
        let ranges = extract_ranges(&map);
        assert_eq!(
            ranges,
            vec![
                (10, 15, 1),
                (15, 16, 2),
                (16, 18, 1),
                (18, 20, 2),
                (20, 25, 1),
            ]
        );
    }

    #[test]
    fn test_full_decrement_removal() {
        let mut map = RangeMap::new();
        map.increment(10..20);
        map.decrement(10..20);
        let ranges = extract_ranges(&map);
        assert_eq!(ranges, vec![]);
    }

    #[test]
    fn test_partial_decrement() {
        let mut map = RangeMap::new();
        map.increment(10..20);
        map.increment(15..25);
        map.decrement(15..20); // makes [15..20] refcount = 1
        let ranges = extract_ranges(&map);
        assert_eq!(ranges, vec![(10, 25, 1)]);
    }

    #[test]
    fn test_partial_decrement_to_zero() {
        let mut map = RangeMap::new();
        map.increment(10..20);
        map.increment(20..30);
        map.decrement(15..25); // makes [15..25] refcount = 0
        let ranges = extract_ranges(&map);
        assert_eq!(ranges, vec![(10, 15, 1), (25, 30, 1)]);
    }

    #[test]
    fn test_adjacent_ranges_merge_by_default() {
        let mut map = RangeMap::new();
        map.increment(10..15);
        map.increment(15..20);
        let ranges = extract_ranges(&map);
        assert_eq!(ranges, vec![(10, 20, 1)]);
    }

    #[test]
    fn test_zero_length_insert_is_ignored() {
        let mut map = RangeMap::new();
        map.increment(10..10);
        let ranges = extract_ranges(&map);
        assert_eq!(ranges.len(), 0);
    }

    #[test]
    fn test_decrement_nonexistent_does_nothing() {
        let mut map = RangeMap::new();
        map.decrement(10..20); // No panic
        let ranges = extract_ranges(&map);
        assert_eq!(ranges.len(), 0);
    }

    #[test]
    fn test_decrement_underflows_to_zero() {
        let mut map = RangeMap::new();
        map.increment(10..20);
        map.decrement(10..25); // only [10..20] exists
        let ranges = extract_ranges(&map);
        assert_eq!(ranges.len(), 0);
    }
    #[test]
    fn test_contains_empty_map() {
        let map = RangeMap::new();
        assert!(!map.contains(0..10));
    }

    #[test]
    fn test_contains_single_range() {
        let mut map = RangeMap::new();
        map.increment(10..20);

        // Test contained range
        assert!(map.contains(10..20));
        assert!(map.contains(12..18));

        // Test non-contained ranges
        assert!(!map.contains(0..10));
        assert!(!map.contains(20..30));
        assert!(!map.contains(15..25));
    }

    #[test]
    fn test_contains_partial_overlap() {
        let mut map = RangeMap::new();
        map.increment(10..20);

        // Test partially overlapping ranges
        assert!(map.contains(15..20));
        assert!(map.contains(10..15));
        assert!(!map.contains(5..15));
        assert!(!map.contains(15..25));
    }

    #[test]
    fn test_contains_multiple_ranges() {
        let mut map = RangeMap::new();
        map.increment(10..20);
        map.increment(30..40);

        // Test individual ranges
        assert!(map.contains(10..20));
        assert!(map.contains(30..40));

        // Test subranges
        assert!(map.contains(12..18));
        assert!(map.contains(32..38));

        // Test gap between ranges
        assert!(!map.contains(20..30));

        // Test spanning multiple ranges
        assert!(!map.contains(15..35));
    }

    #[test]
    fn test_contains_nested_ranges() {
        let mut map = RangeMap::new();
        map.increment(10..40);
        map.increment(20..30);

        // Test outer range
        assert!(map.contains(10..40));

        // Test inner range with higher count
        assert!(map.contains(20..30));

        // Test mixed ranges
        assert!(map.contains(15..25));
        assert!(map.contains(25..35));
    }

    #[test]
    fn test_contains_after_decrement() {
        let mut map = RangeMap::new();
        map.increment(10..40);
        map.decrement(20..30);

        // Test remaining ranges
        assert!(map.contains(10..20));
        assert!(map.contains(30..40));

        // Test decremented range
        assert!(!map.contains(20..30));

        // Test spans including decremented range
        assert!(!map.contains(10..40));
    }

    #[test]
    fn test_contains_zero_length_range() {
        let mut map = RangeMap::new();
        map.increment(10..20);

        // Test zero-length ranges
        assert!(!map.contains(15..15));
        assert!(!map.contains(5..5));
        assert!(!map.contains(25..25));
    }

    #[test]
    fn test_contains_edge_cases() {
        let mut map = RangeMap::new();
        map.increment(10..20);

        // Test edge cases
        assert!(map.contains(10..11));
        assert!(map.contains(19..20));
        assert!(!map.contains(9..10));
        assert!(!map.contains(20..21));
    }
    #[test]
    fn test_overlaps_empty_map() {
        let map = RangeMap::new();
        assert!(!map.overlaps(0..10));
    }

    #[test]
    fn test_overlaps_single_range() {
        let mut map = RangeMap::new();
        map.increment(10..20);

        // Test overlapping cases
        assert!(map.overlaps(15..25)); // Right overlap
        assert!(map.overlaps(5..15)); // Left overlap
        assert!(map.overlaps(12..18)); // Inner overlap
        assert!(map.overlaps(5..25)); // Outer overlap
        assert!(map.overlaps(10..20)); // Exact overlap

        // Test non-overlapping cases
        assert!(!map.overlaps(0..10)); // Before
        assert!(!map.overlaps(20..30)); // After
        assert!(!map.overlaps(0..5)); // Well before
        assert!(!map.overlaps(25..30)); // Well after
    }

    #[test]
    fn test_overlaps_multiple_ranges() {
        let mut map = RangeMap::new();
        map.increment(10..20);
        map.increment(30..40);

        // Test overlapping cases
        assert!(map.overlaps(15..25)); // Overlap with first range
        assert!(map.overlaps(35..45)); // Overlap with second range
        assert!(map.overlaps(15..35)); // Overlap spanning gap
        assert!(map.overlaps(5..45)); // Overlap containing both

        // Test non-overlapping cases
        assert!(!map.overlaps(20..30)); // Between ranges
        assert!(!map.overlaps(0..10)); // Before first
        assert!(!map.overlaps(40..50)); // After last
    }

    #[test]
    fn test_overlaps_edge_cases() {
        let mut map = RangeMap::new();
        map.increment(10..20);

        // Test edge cases
        assert!(!map.overlaps(20..21)); // Adjacent after
        assert!(!map.overlaps(9..10)); // Adjacent before
        assert!(map.overlaps(19..21)); // Overlap at end
        assert!(map.overlaps(9..11)); // Overlap at start
        assert!(!map.overlaps(15..15)); // Zero-length range
        assert!(!map.overlaps(0..0)); // Zero-length range outside
    }

    #[test]
    fn test_overlaps_nested_ranges() {
        let mut map = RangeMap::new();
        map.increment(10..40);
        map.increment(20..30);

        // Test nested overlapping cases
        assert!(map.overlaps(15..25)); // Overlap with both ranges
        assert!(map.overlaps(25..35)); // Overlap with outer range
        assert!(map.overlaps(5..15)); // Partial overlap at start
        assert!(map.overlaps(35..45)); // Partial overlap at end
        assert!(map.overlaps(0..50)); // Complete overlap
    }

    #[test]
    fn test_overlaps_after_decrement() {
        let mut map = RangeMap::new();
        map.increment(10..40);
        map.increment(20..30);
        map.decrement(20..30);

        // Test overlaps after decrement
        assert!(map.overlaps(15..25)); // Still overlaps with remaining range
        assert!(map.overlaps(25..35)); // Still overlaps with remaining range
        assert!(map.overlaps(5..45)); // Still overlaps with full range
    }

    #[test]
    fn test_overlaps_with_invalid_ranges() {
        let mut map = RangeMap::new();
        map.increment(10..20);

        // Test invalid ranges
        assert!(!map.overlaps(25..15)); // End before start
        assert!(!map.overlaps(usize::MAX..usize::MAX)); // Max value
        assert!(!map.overlaps(15..15)); // Zero-length range
    }

    #[test]
    fn test_overlaps_consecutive_ranges() {
        let mut map = RangeMap::new();
        map.increment(10..20);
        map.increment(20..30);
        map.increment(30..40);

        // Test overlaps with consecutive ranges
        assert!(map.overlaps(15..25)); // Overlap across first boundary
        assert!(map.overlaps(25..35)); // Overlap across second boundary
        assert!(map.overlaps(5..45)); // Overlap all ranges
        assert!(!map.overlaps(0..10)); // Before first
        assert!(!map.overlaps(40..50)); // After last
    }
}
