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

//! Implementation of range-based mutual exclusion.

use crate::asslice::AsSlice;
use crate::ranges::RangeMap;
use crate::result::{RangelockError, RangelockResult};
use std::cell::UnsafeCell;
use std::ops::Bound;
use std::ops::{Range, RangeBounds};
use std::sync::{Arc, Mutex};

/// A mutex that provides exclusive access to ranges within a container.
///
/// `RangeMutex` allows multiple threads to safely access different non-overlapping
/// ranges of the same container simultaneously. It prevents concurrent access to
/// overlapping ranges while allowing parallel access to disjoint ranges.
///
/// # Examples
///
/// ```rust
/// use rangelock::RangeMutex;
///
/// let buffer = RangeMutex::new(vec![0; 1024]);
///
/// // Lock different ranges
/// let range1 = buffer.try_range(0..100).unwrap();
/// let range2 = buffer.try_range(200..300).unwrap();
///
/// // This would fail because it overlaps with range1
/// assert!(buffer.try_range(50..150).is_err());
/// ```

pub struct RangeMutex<T: AsSlice> {
    inner: Arc<Shared<T>>,
}

impl<T: AsSlice> RangeMutex<T> {
    /// Creates a new `RangeMutex` wrapping the given container.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rangelock::RangeMutex;
    ///
    /// let mutex = RangeMutex::new(vec![0; 1024]);
    /// ```

    pub fn new(inner: T) -> Self {
        Self {
            inner: Arc::new(Shared {
                ranges: Mutex::default(),
                buffer: UnsafeCell::new(inner),
            }),
        }
    }

    /// Attempts to lock a range of the container for exclusive access.
    ///
    /// This method accepts any type that implements `RangeBounds<usize>`, making it
    /// flexible in how ranges can be specified. It will return a guard that provides
    /// access to the specified range if the lock is successful.
    ///
    /// # Arguments
    ///
    /// * `range_bounds` - A range specification that implements `RangeBounds<usize>`
    ///
    /// # Returns
    ///
    /// * `Ok(RangeSliceGuard)` if the range was successfully locked
    /// * `Err(RangelockError)` if the range is already locked or invalid
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rangelock::RangeMutex;
    ///
    /// let mutex = RangeMutex::new(vec![0; 1024]);
    ///
    /// // Various ways to specify ranges
    /// let guard1 = mutex.try_range(0..100);        // exclusive range
    /// let guard2 = mutex.try_range(200..=299);     // inclusive range
    /// let guard3 = mutex.try_range(400..);         // range to end
    /// let guard4 = mutex.try_range(..50);          // range from start
    /// ```
    pub fn try_range<'a, R>(&self, range_bounds: R) -> RangelockResult<RangeMutexSliceGuard<'a, T>>
    where
        R: RangeBounds<usize>,
        T: 'a,
    {
        let buffer = unsafe { &mut *self.inner.buffer.get() };
        let full_len = buffer.as_slice().len();

        // Convert RangeBounds to concrete Range
        let start = match range_bounds.start_bound() {
            Bound::Included(&n) => n,
            Bound::Excluded(&n) => n + 1,
            Bound::Unbounded => 0,
        };
        let end = match range_bounds.end_bound() {
            Bound::Included(&n) => n + 1,
            Bound::Excluded(&n) => n,
            Bound::Unbounded => full_len,
        };

        // Check bounds
        if start > end || end > full_len {
            return Err(RangelockError::RangeNotAllocated);
        }

        let range = start..end;

        // Lock the range mutex for checkout
        let mut ranges = self.inner.ranges.lock().unwrap();

        // Test if locking a range is possible
        if ranges.overlaps(range.clone()) {
            Err(RangelockError::RangeAlreadyLocked)
        } else {
            ranges.increment(range.clone());
            let slice = unsafe { &mut (*self.inner.buffer.get()).as_slice_mut()[range.clone()] };

            Ok(RangeMutexSliceGuard {
                inner: self.inner.clone(),
                range,
                slice,
            })
        }
    }

    /// Attempts to acquire an exclusive lock on the entire container.
    ///
    /// This method tries to lock the complete container, returning a `RangeMutexGuard` that
    /// provides exclusive access to all contents. Unlike `try_range`, this method locks
    /// the entire container rather than a specific range.
    ///
    /// # Returns
    ///
    /// * `Ok(RangeMutexGuard)` - If the lock was successfully acquired
    /// * `Err(RangelockError::RangeAlreadyLocked)` - If any part of the container is currently locked
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rangelock::RangeMutex;
    ///
    /// let mutex = RangeMutex::new(vec![0; 1024]);
    ///
    /// // Acquire full lock
    /// let guard = mutex.try_mutex().unwrap();
    ///
    /// // While holding the full lock, no other locks can be acquired
    /// assert!(mutex.try_range(0..100).is_err());
    /// assert!(mutex.try_mutex().is_err());
    /// ```
    ///
    /// # Thread Safety
    ///
    /// When the lock is acquired:
    /// - No other thread can acquire a range lock via `try_range`
    /// - No other thread can acquire a full lock via `try_mutex`
    /// - The lock is automatically released when the guard is dropped
    ///
    /// # Note
    ///
    /// This method is useful when you need to perform operations that require access
    /// to the entire container atomically. If you only need access to a specific range,
    /// consider using `try_range` instead to allow for better concurrency.
    pub fn try_mutex<'a>(&self) -> RangelockResult<RangeMutexGuard<'a, T>> {
        let buffer = unsafe { &mut *self.inner.buffer.get() };
        let full_len = buffer.as_slice().len();

        // Lock the range mutex for checkout
        let mut ranges = self.inner.ranges.lock().unwrap();

        // Test if locking a range is possible
        if ranges.overlaps(0..full_len) {
            Err(RangelockError::RangeAlreadyLocked)
        } else {
            ranges.increment(0..full_len);
            Ok(RangeMutexGuard {
                inner: self.inner.clone(),
                slice: buffer,
            })
        }
    }
}

impl<T: AsSlice> std::fmt::Debug for RangeMutex<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "RangeMutex {{ .. }}")
    }
}

unsafe impl<T: AsSlice> Send for RangeMutex<T> {}

unsafe impl<T: AsSlice> Sync for RangeMutex<T> {}

struct Shared<T: AsSlice> {
    ranges: Mutex<RangeMap>,
    buffer: UnsafeCell<T>,
}

/// A RAII guard providing access to a locked range of data.
///
/// When this guard is dropped, the range lock is automatically released.
pub struct RangeMutexSliceGuard<'a, T: AsSlice> {
    inner: Arc<Shared<T>>,
    range: Range<usize>,
    slice: &'a mut [T::Item],
}

impl<'a, T: AsSlice> RangeMutexSliceGuard<'a, T> {
    /// Returns the range that this guard is locking.
    pub fn range(&self) -> Range<usize> {
        self.range.clone()
    }

    /// Returns an immutable reference to the locked slice.
    pub fn as_ref(&self) -> &[T::Item] {
        self.slice.as_ref()
    }

    /// Returns a mutable reference to the locked slice.
    pub fn as_mut(&mut self) -> &mut [T::Item] {
        self.slice.as_mut()
    }
}

impl<'a, T: AsSlice> std::fmt::Debug for RangeMutexSliceGuard<'a, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "RangeSliceGuard {{ .. }}")
    }
}

impl<'a, T: AsSlice> Drop for RangeMutexSliceGuard<'a, T> {
    fn drop(&mut self) {
        let ranges = self.inner.ranges.lock();
        ranges.unwrap().decrement(self.range.clone());
    }
}

/// A RAII guard that provides exclusive access to the entire contents of a `RangeMutex`.
///
/// When this guard is dropped, the lock is automatically released. Unlike `RangeSliceGuard`,
/// this guard locks the entire container rather than just a specific range.
///
/// The guard implements `Deref` and `DerefMut` to provide easy access to the protected data.
///
/// # Examples
///
/// ```rust
/// use rangelock::RangeMutex;
///
/// let mutex = RangeMutex::new(vec![0; 1024]);
///
/// // Lock the entire container
/// let mut guard = mutex.try_mutex().unwrap();
///
/// // Access the data through deref
/// guard[0] = 42;
///
/// // The lock is automatically released when the guard is dropped
/// drop(guard);
/// ```
///
/// # Thread Safety
///
/// The guard ensures exclusive access to the entire container, preventing any other threads
/// from acquiring either range-based locks or full mutex locks while this guard is active.
///
/// # Note
///
/// While `RangeSliceGuard` allows multiple non-overlapping ranges to be locked simultaneously,
/// `RangeMutexGuard` locks the entire container, providing exclusive access to all of its contents.
/// This is useful when you need to perform operations on the entire container atomically.
pub struct RangeMutexGuard<'a, T: AsSlice> {
    inner: Arc<Shared<T>>,
    slice: &'a mut T,
}

impl<'a, T: AsSlice> std::fmt::Debug for RangeMutexGuard<'a, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "RangeMutexGuard {{ .. }}")
    }
}

impl<'a, T: AsSlice> std::ops::Deref for RangeMutexGuard<'a, T> {
    type Target = T;
    fn deref(&self) -> &T {
        self.slice
    }
}

impl<'a, T: AsSlice> std::ops::DerefMut for RangeMutexGuard<'a, T> {
    fn deref_mut(&mut self) -> &mut T {
        &mut self.slice
    }
}

impl<'a, T: AsSlice> Drop for RangeMutexGuard<'a, T> {
    fn drop(&mut self) {
        let ranges = self.inner.ranges.lock();
        let full_len = self.slice.as_slice().len();
        ranges.unwrap().decrement(0..full_len);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Arc;
    use std::thread;

    #[test]
    fn test_basic_range_locking() {
        let mutex = RangeMutex::new(vec![0; 100]);
        let guard = mutex.try_range(0..50).unwrap();
        assert_eq!(guard.range(), 0..50);
    }

    #[test]
    fn test_overlapping_ranges() {
        let mutex = RangeMutex::new(vec![0; 100]);
        let guard1 = mutex.try_range(0..50).unwrap();
        let guard2 = mutex.try_range(25..75);
        assert!(guard2.is_err());
        assert!(matches!(
            guard2.unwrap_err(),
            RangelockError::RangeAlreadyLocked
        ));
    }

    #[test]
    fn test_non_overlapping_ranges() {
        let mutex = RangeMutex::new(vec![0; 100]);
        let guard1 = mutex.try_range(0..25).unwrap();
        let guard2 = mutex.try_range(25..50).unwrap();
        assert_eq!(guard1.range(), 0..25);
        assert_eq!(guard2.range(), 25..50);
    }

    #[test]
    fn test_out_of_bounds() {
        let mutex = RangeMutex::new(vec![0; 100]);
        let guard = mutex.try_range(90..110);
        assert!(guard.is_err());
        assert!(matches!(
            guard.unwrap_err(),
            RangelockError::RangeNotAllocated
        ));
    }

    #[test]
    fn test_empty_range() {
        let mutex = RangeMutex::new(vec![0; 100]);
        let guard = mutex.try_range(50..50);
        assert!(guard.is_ok());
    }

    #[test]
    fn test_range_modification() {
        let mutex = RangeMutex::new(vec![0; 100]);
        {
            let mut guard = mutex.try_range(0..50).unwrap();
            for i in guard.as_mut() {
                *i = 1;
            }
        }
        let guard = mutex.try_range(0..50).unwrap();
        assert!(guard.as_ref().iter().all(|&x| x == 1));
    }

    #[test]
    fn test_multiple_threads() {
        let mutex = Arc::new(RangeMutex::new(vec![0; 100]));
        let mut handles = vec![];

        // Spawn 10 threads, each working on a different range
        for i in 0..10 {
            let mutex = Arc::clone(&mutex);
            let handle = thread::spawn(move || {
                let start = i * 10;
                let end = start + 10;
                let mut guard = mutex.try_range(start..end).unwrap();
                for val in guard.as_mut() {
                    *val = i as u8;
                }
            });
            handles.push(handle);
        }

        // Wait for all threads to complete
        for handle in handles {
            handle.join().unwrap();
        }

        // Verify results
        let guard = mutex.try_range(0..100).unwrap();
        for i in 0..10 {
            let slice = &guard.as_ref()[i * 10..(i + 1) * 10];
            assert!(slice.iter().all(|&x| x == i as u8));
        }
    }

    #[test]
    fn test_guard_drop_releases_lock() {
        let mutex = RangeMutex::new(vec![0; 100]);
        {
            let _guard = mutex.try_range(0..50).unwrap();
        }
        // After guard is dropped, we should be able to lock the same range again
        assert!(mutex.try_range(0..50).is_ok());
    }

    #[test]
    fn test_inclusive_range() {
        let mutex = RangeMutex::new(vec![0; 100]);
        let guard = mutex.try_range(0..=49);
        assert!(guard.is_ok());
        assert_eq!(guard.unwrap().range(), 0..50);
    }

    #[test]
    fn test_range_from() {
        let mutex = RangeMutex::new(vec![0; 100]);
        let guard = mutex.try_range(50..);
        assert!(guard.is_ok());
        assert_eq!(guard.unwrap().range(), 50..100);
    }

    #[test]
    fn test_range_to() {
        let mutex = RangeMutex::new(vec![0; 100]);
        let guard = mutex.try_range(..50);
        assert!(guard.is_ok());
        assert_eq!(guard.unwrap().range(), 0..50);
    }

    #[test]
    fn test_full_range() {
        let mutex = RangeMutex::new(vec![0; 100]);
        let guard = mutex.try_range(..);
        assert!(guard.is_ok());
        assert_eq!(guard.unwrap().range(), 0..100);
    }

    #[test]
    fn test_concurrent_disjoint_modifications() {
        let mutex = Arc::new(RangeMutex::new(vec![0; 100]));
        let mut handles = vec![];

        // Create pairs of threads working on adjacent ranges
        for i in 0..5 {
            let mutex1 = Arc::clone(&mutex);
            let mutex2 = Arc::clone(&mutex);

            // First thread of the pair
            let handle1 = thread::spawn(move || {
                let start = i * 20;
                let end = start + 10;
                let mut guard = mutex1.try_range(start..end).unwrap();
                for val in guard.as_mut() {
                    *val = 1;
                }
            });

            // Second thread of the pair
            let handle2 = thread::spawn(move || {
                let start = i * 20 + 10;
                let end = start + 10;
                let mut guard = mutex2.try_range(start..end).unwrap();
                for val in guard.as_mut() {
                    *val = 2;
                }
            });

            handles.push(handle1);
            handles.push(handle2);
        }

        // Wait for all threads to complete
        for handle in handles {
            handle.join().unwrap();
        }

        // Verify results
        let guard = mutex.try_range(0..100).unwrap();
        for chunk in guard.as_ref().chunks(20) {
            assert!(chunk[0..10].iter().all(|&x| x == 1));
            assert!(chunk[10..20].iter().all(|&x| x == 2));
        }
    }

    #[test]
    fn test_send_sync() {
        fn assert_send_sync<T: Send + Sync>() {}
        assert_send_sync::<RangeMutex<Vec<u8>>>();
    }
}
