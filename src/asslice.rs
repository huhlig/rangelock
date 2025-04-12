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


//! Trait definitions for slice-like access to contiguous data structures.

/// A trait for types that can be viewed as a contiguous slice of elements.
///
/// This trait provides a unified interface for accessing data as both immutable
/// and mutable slices, making it possible to implement range-based locking
/// for any container that can provide slice views of its data.
///
/// # Examples
///
/// ```rust
/// use rangelock::AsSlice;
///
/// // Vec<T> implements AsSlice
/// let mut vec = vec![1, 2, 3, 4, 5];
/// assert_eq!(vec.length(), 5);
/// assert_eq!(vec.as_slice(), &[1, 2, 3, 4, 5]);
///
/// // Modify through mutable slice
/// vec.as_slice_mut()[0] = 10;
/// assert_eq!(vec[0], 10);
/// ```
pub trait AsSlice {
    /// The type of elements contained in the slice.
    type Item;

    /// Returns the length of the slice.
    fn length(&self) -> usize;

    /// Returns an immutable reference to the slice.
    fn as_slice(&self) -> &[Self::Item];

    /// Returns a mutable reference to the slice.
    fn as_slice_mut(&mut self) -> &mut [Self::Item];

}

// Implementation for slices
impl<T> AsSlice for [T] {
    type Item = T;
    fn length(&self) -> usize {
        self.len()
    }
    fn as_slice(&self) -> &[Self::Item] {
        self.as_ref()
    }
    fn as_slice_mut(&mut self) -> &mut [Self::Item] {
        self.as_mut()
    }
}

// Implementation for Vec<T>
impl<'a, T> AsSlice for Vec<T> {
    type Item = T;
    fn length(&self) -> usize {
        self.len()
    }
    fn as_slice(&self) -> &[Self::Item] {
        self.as_slice()
    }
    fn as_slice_mut(&mut self) -> &mut [Self::Item] {
        self.as_mut_slice()
    }
}
