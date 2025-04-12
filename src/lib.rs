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

//! # Rangelock
//!
//! A Rust library providing fine-grained concurrent access to slices of data through range-based
//! locking mechanisms. It offers both read-write (RwLock) and exclusive (Mutex) access patterns
//! that operate on specific ranges within a container.
//!
//! ## Key Features
//!
//! - **Range-based Access Control**: Lock specific ranges of data instead of entire containers
//! - **Multiple Access Patterns**: Supports both read-write (RwLock) and exclusive (Mutex) locking
//! - **Concurrent Range Access**: Different threads can safely access non-overlapping ranges
//! - **RAII Guards**: Automatic lock release through guard pattern
//! - **Flexible Range Specification**: Supports various range syntax including inclusive, exclusive, and unbounded ranges
//! - **Generic Container Support**: Works with any type implementing the `AsSlice` trait
//!
//! ## Usage Examples
//!
//! ### Basic RwLock Usage
//!
//! ```rust
//! use rangelock::RangeRwlock;
//!
//! // Create a new RangeRwlock with a vector
//! let data = RangeRwlock::new(vec![0; 1000]);
//!
//! // Acquire read access to a range
//! let reader = data.try_read(0..100).unwrap();
//! assert_eq!(reader.as_ref(), &[0; 100]);
//!
//! // Acquire write access to a non-overlapping range
//! let mut writer = data.try_write(200..300).unwrap();
//! writer.as_mut().fill(1);
//!
//! // Multiple readers can access the same range
//! let another_reader = data.try_read(0..100).unwrap();
//! ```
//!
//! ### Basic Mutex Usage
//!
//! ```rust
//! use rangelock::RangeMutex;
//!
//! // Create a new RangeMutex with a vector
//! let data = RangeMutex::new(vec![0; 1000]);
//!
//! // Lock a specific range
//! let mut guard = data.try_range(0..100).unwrap();
//! guard.as_mut().fill(1);
//!
//! // Other ranges can be locked simultaneously
//! let other_guard = data.try_range(200..300).unwrap();
//! ```
//!
//! ## Lock Types
//!
//! ### RangeRwlock
//!
//! Provides read-write locking functionality with the following characteristics:
//!
//! - Multiple readers can access the same range simultaneously
//! - Only one writer can access a range at a time
//! - Readers and writers cannot access the same range simultaneously
//! - Different ranges can be accessed concurrently
//!
//! ### RangeMutex
//!
//! Provides exclusive locking functionality with the following characteristics:
//!
//! - Only one thread can access a range at a time
//! - Different ranges can be locked by different threads simultaneously
//! - Full container locking available through `try_mutex()`
//!
//! ## Range Specifications
//!
//! Both lock types support flexible range specifications:
//!
//! ```rust
//! use rangelock::RangeRwlock;
//!
//! let data = RangeRwlock::new(vec![0; 1000]);
//!
//! // Exclusive range
//! let guard1 = data.try_read(0..100);
//!
//! // Inclusive range
//! let guard2 = data.try_read(200..=299);
//!
//! // Range from start
//! let guard3 = data.try_read(..300);
//!
//! // Range to end
//! let guard4 = data.try_read(900..);
//!
//! // Full range
//! let guard5 = data.try_read(..);
//! ```
//!
//! ## Custom Container Support
//!
//! To use a custom container type with rangelock, implement the `AsSlice` trait:
//!
//! ```rust
//! use rangelock::AsSlice;
//!
//! struct MyContainer<T> {
//!     data: Vec<T>,
//! }
//!
//! impl<T> AsSlice for MyContainer<T> {
//!     type Item = T;
//!
//!     fn length(&self) -> usize {
//!         self.data.len()
//!     }
//!
//!     fn as_slice(&self) -> &[Self::Item] {
//!         &self.data
//!     }
//!
//!     fn as_slice_mut(&mut self) -> &mut [Self::Item] {
//!         &mut self.data
//!     }
//! }
//! ```
//!
//! ## Error Handling
//!
//! Operations return `RangelockResult<T>` which can contain the following errors:
//!
//! - `RangelockError::RangeAlreadyLocked`: The requested range is already locked
//! - `RangelockError::RangeNotAllocated`: The requested range is invalid or out of bounds
//!
//! ## Thread Safety
//!
//! All lock types implement `Send` and `Sync`, making them safe to use across thread boundaries.
//! The RAII guard pattern ensures that locks are properly released even in the presence of panics.
//!
//! ## Performance Considerations
//!
//! - Range-based locking allows for better concurrency than whole-container locks
//! - Non-overlapping ranges can be accessed simultaneously
//! - Consider using larger ranges to reduce lock overhead when accessing multiple adjacent elements
//! - Use `try_mutex()` when you need to operate on the entire container atomically
//!
//! ## License
//!
//! Licensed under the Apache License, Version 2.0.

#![warn(
    clippy::cargo,
    missing_docs,
    clippy::pedantic,
    future_incompatible,
    rust_2018_idioms
)]
#![allow(
    clippy::option_if_let_else,
    clippy::module_name_repetitions,
    clippy::missing_errors_doc
)]
// Using stable range APIs
// TODO: Remove These before 1.0
#![allow(unused_imports, unused_variables, dead_code, unused_mut)]

mod asslice;
mod mutex;
mod ranges;
mod result;
mod rwlock;

pub use self::asslice::AsSlice;
pub use self::mutex::{RangeMutex, RangeMutexGuard, RangeMutexSliceGuard};
pub use self::ranges::RangeMap;
pub use self::result::{RangelockError, RangelockResult};
pub use self::rwlock::{
    RangeRwlock, RangeRwlockMutexGuard, RangeRwlockSliceReadGuard, RangeRwlockSliceWriteGuard,
};
