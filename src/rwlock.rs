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

//! Implementation of range-based Read-Write Lock.

use crate::asslice::AsSlice;
use crate::ranges::RangeMap;
use crate::result::{RangelockError, RangelockResult};
use std::cell::UnsafeCell;
use std::ops::Bound;
use std::ops::{Range, RangeBounds};
use std::sync::{Arc, Mutex};

/// A range-based read-write lock that provides concurrent access to different ranges of a container.
///
/// `RangeRwlock` allows multiple threads to safely access different ranges of the same container
/// simultaneously, with support for both read and write access. It follows the multiple-reader,
/// single-writer pattern for each range, while allowing concurrent access to non-overlapping ranges.
///
/// # Features
///
/// - Multiple readers can access the same range simultaneously
/// - Only one writer can access a range at a time
/// - Different ranges can be read or written concurrently
/// - Full container lock available through `try_mutex`
/// - RAII-style guards ensure automatic lock release
///
/// # Examples
///
/// ```rust
/// use rangelock::RangeRwlock;
///
/// // Create a new RangeRwlock containing a vector
/// let rwlock = RangeRwlock::new(vec![0; 1024]);
///
/// // Acquire read access to a range
/// let read_guard = rwlock.try_read(0..100).unwrap();
///
/// // Acquire write access to a non-overlapping range
/// let write_guard = rwlock.try_write(200..300).unwrap();
///
/// // Multiple readers can access the same range
/// let another_read = rwlock.try_read(0..100).unwrap();
///
/// // But writing to an already locked range will fail
/// assert!(rwlock.try_write(50..150).is_err());
/// ```
pub struct RangeRwlock<T: AsSlice> {
    inner: Arc<Shared<T>>,
}

impl<T: AsSlice> RangeRwlock<T> {
    /// Creates a new `RangeRwlock` containing the given data.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rangelock::RangeRwlock;
    ///
    /// let rwlock = RangeRwlock::new(vec![0; 1024]);
    /// ```
    pub fn new(inner: T) -> Self {
        Self {
            inner: Arc::new(Shared {
                ranges: Mutex::new(Ranges {
                    reads: Default::default(),
                    writes: Default::default(),
                }),
                buffer: UnsafeCell::new(inner),
            }),
        }
    }

    /// Attempts to acquire a read lock on a range of the container.
    ///
    /// # Arguments
    ///
    /// * `range_bounds` - A range specification that implements `RangeBounds<usize>`
    ///
    /// # Returns
    ///
    /// * `Ok(RangeRwlockSliceReadGuard)` if the lock was successfully acquired
    /// * `Err(RangelockError)` if the range is write-locked or invalid
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rangelock::RangeRwlock;
    ///
    /// let rwlock = RangeRwlock::new(vec![0; 1024]);
    ///
    /// // Various ways to specify ranges
    /// let guard1 = rwlock.try_read(0..100);        // exclusive range
    /// let guard2 = rwlock.try_read(200..=299);     // inclusive range
    /// let guard3 = rwlock.try_read(400..);         // range to end
    /// let guard4 = rwlock.try_read(..50);          // range from start
    /// ```
    pub fn try_read<'a, R>(
        &self,
        range_bounds: R,
    ) -> RangelockResult<RangeRwlockSliceReadGuard<'a, T>>
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

        // Test if locking a range is possible (reads and writes cannot co-exist)
        if ranges.writes.overlaps(range.clone()) {
            Err(RangelockError::RangeAlreadyLocked)
        } else {
            ranges.reads.increment(range.clone());
            let slice = unsafe { &(*self.inner.buffer.get()).as_slice()[range.clone()] };

            Ok(RangeRwlockSliceReadGuard {
                inner: self.inner.clone(),
                range,
                slice,
            })
        }
    }

    /// Attempts to acquire a write lock on a range of the container.
    ///
    /// # Arguments
    ///
    /// * `range_bounds` - A range specification that implements `RangeBounds<usize>`
    ///
    /// # Returns
    ///
    /// * `Ok(RangeRwlockSliceWriteGuard)` if the lock was successfully acquired
    /// * `Err(RangelockError)` if the range is already locked (read or write) or invalid
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rangelock::RangeRwlock;
    ///
    /// let rwlock = RangeRwlock::new(vec![0; 1024]);
    ///
    /// // Lock a range for writing
    /// let mut guard = rwlock.try_write(0..100).unwrap();
    ///
    /// // Modify the locked range
    /// guard.as_mut().fill(42);
    /// ```
    pub fn try_write<'a, R>(
        &self,
        range_bounds: R,
    ) -> RangelockResult<RangeRwlockSliceWriteGuard<'a, T>>
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
        if ranges.reads.overlaps(range.clone()) {
            Err(RangelockError::RangeAlreadyLocked)
        } else if ranges.writes.overlaps(range.clone()) {
            Err(RangelockError::RangeAlreadyLocked)
        } else {
            ranges.writes.increment(range.clone());
            let slice = unsafe { &mut (*self.inner.buffer.get()).as_slice_mut()[range.clone()] };

            Ok(RangeRwlockSliceWriteGuard {
                inner: self.inner.clone(),
                range,
                slice,
            })
        }
    }

    /// Attempts to acquire an exclusive lock on the entire container.
    ///
    /// # Returns
    ///
    /// * `Ok(RangeRwlockMutexGuard)` if the lock was successfully acquired
    /// * `Err(RangelockError)` if any part of the container is currently locked
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rangelock::{AsSlice, RangeRwlock};
    ///
    /// let rwlock = RangeRwlock::new(vec![0; 1024]);
    ///
    /// // Acquire exclusive access to the entire container
    /// let mut guard = rwlock.try_mutex().unwrap();
    ///
    /// // Modify the entire container
    /// guard.as_slice_mut().fill(42);
    /// ```
    pub fn try_mutex<'a>(&self) -> RangelockResult<RangeRwlockMutexGuard<'a, T>> {
        let buffer = unsafe { &mut *self.inner.buffer.get() };
        let full_len = buffer.as_slice().len();

        // Lock the range mutex for checkout
        let mut ranges = self.inner.ranges.lock().unwrap();

        // Test if locking a range is possible
        if ranges.reads.overlaps(0..full_len) {
            Err(RangelockError::RangeAlreadyLocked)
        } else if ranges.writes.overlaps(0..full_len) {
            Err(RangelockError::RangeAlreadyLocked)
        } else {
            ranges.writes.increment(0..full_len);
            Ok(RangeRwlockMutexGuard {
                inner: self.inner.clone(),
                slice: buffer,
            })
        }
    }
}

impl<T: AsSlice> std::fmt::Debug for RangeRwlock<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "RangeRwlock {{ .. }}")
    }
}

unsafe impl<T: AsSlice> Send for RangeRwlock<T> {}

unsafe impl<T: AsSlice> Sync for RangeRwlock<T> {}

struct Shared<T: AsSlice> {
    ranges: Mutex<Ranges>,
    buffer: UnsafeCell<T>,
}

struct Ranges {
    reads: RangeMap,
    writes: RangeMap,
}

/// A RAII guard providing read-only access to a locked range of data.
///
/// This guard is created by the [`RangeRwlock::try_read`] method of [`RangeRwlock`]. When the guard
/// is dropped, the read lock is automatically released.
///
/// # Multiple Readers
///
/// Multiple `RangeRwlockSliceReadGuard`s can exist for the same range simultaneously,
/// allowing concurrent read access from multiple threads.
///
/// # Examples
///
/// ```rust
/// use rangelock::RangeRwlock;
///
/// let rwlock = RangeRwlock::new(vec![1, 2, 3, 4, 5]);
/// let guard = rwlock.try_read(1..4).unwrap();
///
/// // Read access to the locked range
/// assert_eq!(guard.as_ref(), &[2, 3, 4]);
///
/// // Get the range that this guard is locking
/// assert_eq!(guard.range(), 1..4);
/// ```
pub struct RangeRwlockSliceReadGuard<'a, T: AsSlice> {
    inner: Arc<Shared<T>>,
    range: Range<usize>,
    slice: &'a [T::Item],
}

impl<'a, T: AsSlice> RangeRwlockSliceReadGuard<'a, T> {
    /// Returns the range that this guard is locking.
    pub fn range(&self) -> Range<usize> {
        self.range.clone()
    }

    /// Returns an immutable reference to the locked slice.
    pub fn as_ref(&self) -> &[T::Item] {
        self.slice.as_ref()
    }
}

impl<'a, T: AsSlice> std::fmt::Debug for RangeRwlockSliceReadGuard<'a, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "RangeRwlockSliceReadGuard {{ .. }}")
    }
}

impl<'a, T: AsSlice> Drop for RangeRwlockSliceReadGuard<'a, T> {
    fn drop(&mut self) {
        let ranges = self.inner.ranges.lock();
        ranges.unwrap().reads.decrement(self.range.clone());
    }
}

/// A RAII guard providing mutable access to a locked range of data.
///
/// This guard is created by the [`RangeRwlock::try_write`] method of [`RangeRwlock`]. When the 
/// guard is dropped, the write lock is automatically released.
///
/// # Exclusive Access
///
/// While this guard exists:
/// - No other write guards can exist for overlapping ranges
/// - No read guards can exist for overlapping ranges
/// - Other ranges can still be independently read or written
///
/// # Examples
///
/// ```rust
/// use rangelock::RangeRwlock;
///
/// let rwlock = RangeRwlock::new(vec![0; 5]);
/// let mut guard = rwlock.try_write(1..4).unwrap();
///
/// // Modify the locked range
/// guard.as_mut().copy_from_slice(&[1, 2, 3]);
///
/// // Get the range that this guard is locking
/// assert_eq!(guard.range(), 1..4);
/// ```
pub struct RangeRwlockSliceWriteGuard<'a, T: AsSlice> {
    inner: Arc<Shared<T>>,
    range: Range<usize>,
    slice: &'a mut [T::Item],
}

impl<'a, T: AsSlice> RangeRwlockSliceWriteGuard<'a, T> {
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

impl<'a, T: AsSlice> std::fmt::Debug for RangeRwlockSliceWriteGuard<'a, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "RangeRwlockSliceReadGuard {{ .. }}")
    }
}

impl<'a, T: AsSlice> Drop for RangeRwlockSliceWriteGuard<'a, T> {
    fn drop(&mut self) {
        let ranges = self.inner.ranges.lock();
        ranges.unwrap().writes.decrement(self.range.clone());
    }
}

/// A RAII guard providing exclusive access to the entire contents of a `RangeRwlock`.
///
/// This guard is created by the [`RangeRwlock::try_mutex`] method of [`RangeRwlock`]. It provides
/// complete mutable access to the underlying container, preventing any other access
/// while the guard exists.
///
/// # Exclusive Access
///
/// While this guard exists:
/// - No other mutex guards can exist
/// - No read guards can exist for any range
/// - No write guards can exist for any range
///
/// # Examples
///
/// ```rust
/// use rangelock::{RangeRwlock, AsSlice};
///
/// let rwlock = RangeRwlock::new(vec![0; 5]);
///
/// // Lock the entire container
/// let mut guard = rwlock.try_mutex().unwrap();
///
/// // Modify the entire container
/// guard.as_slice_mut().copy_from_slice(&[1, 2, 3, 4, 5]);
///
/// // All other access attempts will fail while the mutex guard exists
/// assert!(rwlock.try_read(0..2).is_err());
/// assert!(rwlock.try_write(3..5).is_err());
/// ```
pub struct RangeRwlockMutexGuard<'a, T: AsSlice> {
    inner: Arc<Shared<T>>,
    slice: &'a mut T,
}

impl<'a, T: AsSlice> std::fmt::Debug for RangeRwlockMutexGuard<'a, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "RangeRwlockMutexGuard {{ .. }}")
    }
}

impl<'a, T: AsSlice> std::ops::Deref for RangeRwlockMutexGuard<'a, T> {
    type Target = T;
    fn deref(&self) -> &T {
        self.slice
    }
}

impl<'a, T: AsSlice> std::ops::DerefMut for RangeRwlockMutexGuard<'a, T> {
    fn deref_mut(&mut self) -> &mut T {
        &mut self.slice
    }
}

impl<'a, T: AsSlice> Drop for RangeRwlockMutexGuard<'a, T> {
    fn drop(&mut self) {
        let ranges = self.inner.ranges.lock();
        let full_len = self.slice.as_slice().len();
        ranges.unwrap().writes.decrement(0..full_len);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Arc;
    use std::thread;

    #[test]
    fn test_basic_read_lock() {
        let rwlock = RangeRwlock::new(vec![1; 100]);
        let guard = rwlock.try_read(0..50).unwrap();
        assert_eq!(guard.range(), 0..50);
        assert!(guard.as_ref().iter().all(|&x| x == 1));
    }

    #[test]
    fn test_basic_write_lock() {
        let rwlock = RangeRwlock::new(vec![0; 100]);
        let mut guard = rwlock.try_write(0..50).unwrap();
        for i in guard.as_mut() {
            *i = 1;
        }
        assert_eq!(guard.range(), 0..50);
        assert!(guard.as_ref().iter().all(|&x| x == 1));
    }

    #[test]
    fn test_multiple_read_locks() {
        let rwlock = RangeRwlock::new(vec![1; 100]);
        let guard1 = rwlock.try_read(0..25).unwrap();
        let guard2 = rwlock.try_read(25..50).unwrap();
        let guard3 = rwlock.try_read(0..25).unwrap(); // Should allow multiple reads on same range

        assert_eq!(guard1.range(), 0..25);
        assert_eq!(guard2.range(), 25..50);
        assert_eq!(guard3.range(), 0..25);
    }

    #[test]
    fn test_write_lock_blocks_read() {
        let rwlock = RangeRwlock::new(vec![0; 100]);
        let write_guard = rwlock.try_write(0..50).unwrap();
        let read_result = rwlock.try_read(0..50);
        assert!(matches!(
            read_result,
            Err(RangelockError::RangeAlreadyLocked)
        ));
    }

    #[test]
    fn test_read_lock_blocks_write() {
        let rwlock = RangeRwlock::new(vec![0; 100]);
        let read_guard = rwlock.try_read(0..50).unwrap();
        let write_result = rwlock.try_write(0..50);
        assert!(matches!(
            write_result,
            Err(RangelockError::RangeAlreadyLocked)
        ));
    }

    #[test]
    fn test_overlapping_write_locks() {
        let rwlock = RangeRwlock::new(vec![0; 100]);
        let guard1 = rwlock.try_write(0..50).unwrap();
        let guard2 = rwlock.try_write(25..75);
        assert!(matches!(guard2, Err(RangelockError::RangeAlreadyLocked)));
    }

    #[test]
    fn test_mutex_lock() {
        let rwlock = RangeRwlock::new(vec![0; 100]);
        let mut guard = rwlock.try_mutex().unwrap();
        guard.as_slice_mut().iter_mut().for_each(|x| *x = 1);
        assert!(guard.as_slice().iter().all(|&x| x == 1));
    }

    #[test]
    fn test_mutex_blocks_all() {
        let rwlock = RangeRwlock::new(vec![0; 100]);
        let mutex_guard = rwlock.try_mutex().unwrap();

        assert!(matches!(
            rwlock.try_read(0..50),
            Err(RangelockError::RangeAlreadyLocked)
        ));
        assert!(matches!(
            rwlock.try_write(0..50),
            Err(RangelockError::RangeAlreadyLocked)
        ));
        assert!(matches!(
            rwlock.try_mutex(),
            Err(RangelockError::RangeAlreadyLocked)
        ));
    }

    #[test]
    fn test_concurrent_reads() {
        let rwlock = Arc::new(RangeRwlock::new(vec![1; 100]));
        let mut handles = vec![];

        for i in 0..5 {
            let rwlock = Arc::clone(&rwlock);
            let handle = thread::spawn(move || {
                let start = i * 20;
                let guard = rwlock.try_read(start..start + 20).unwrap();
                assert!(guard.as_ref().iter().all(|&x| x == 1));
            });
            handles.push(handle);
        }

        for handle in handles {
            handle.join().unwrap();
        }
    }

    #[test]
    fn test_concurrent_disjoint_writes() {
        let rwlock = Arc::new(RangeRwlock::new(vec![0; 100]));
        let mut handles = vec![];

        for i in 0..5 {
            let rwlock = Arc::clone(&rwlock);
            let handle = thread::spawn(move || {
                let start = i * 20;
                let mut guard = rwlock.try_write(start..start + 20).unwrap();
                guard.as_mut().iter_mut().for_each(|x| *x = i as u8);
            });
            handles.push(handle);
        }

        for handle in handles {
            handle.join().unwrap();
        }

        // Verify results
        let guard = rwlock.try_read(0..100).unwrap();
        for (i, chunk) in guard.as_ref().chunks(20).enumerate() {
            assert!(chunk.iter().all(|&x| x == i as u8));
        }
    }

    #[test]
    fn test_out_of_bounds() {
        let rwlock = RangeRwlock::new(vec![0; 100]);
        assert!(matches!(
            rwlock.try_read(90..110),
            Err(RangelockError::RangeNotAllocated)
        ));
        assert!(matches!(
            rwlock.try_write(90..110),
            Err(RangelockError::RangeNotAllocated)
        ));
    }

    #[test]
    fn test_guard_drop_releases_lock() {
        let rwlock = RangeRwlock::new(vec![0; 100]);
        {
            let _write_guard = rwlock.try_write(0..50).unwrap();
        }
        // After guard is dropped, we should be able to acquire both read and write locks
        assert!(rwlock.try_read(0..50).is_ok());
        assert!(rwlock.try_write(0..50).is_ok());
    }

    #[test]
    fn test_inclusive_range_bounds() {
        let rwlock = RangeRwlock::new(vec![0; 100]);
        let read_guard = rwlock.try_read(0..=49).unwrap();
        assert_eq!(read_guard.range(), 0..50);

        let write_guard = rwlock.try_write(50..=99).unwrap();
        assert_eq!(write_guard.range(), 50..100);
    }

    #[test]
    fn test_unbounded_ranges() {
        let rwlock = RangeRwlock::new(vec![0; 100]);

        let read_start = rwlock.try_read(50..).unwrap();
        assert_eq!(read_start.range(), 50..100);

        {
            let write_end = rwlock.try_write(..50).unwrap();
            assert_eq!(write_end.range(), 0..50);
        } // write lock is dropped here

        let read_full = rwlock.try_read(..).unwrap();
        assert_eq!(read_full.range(), 0..100);
    }

    #[test]
    fn test_send_sync() {
        fn assert_send_sync<T: Send + Sync>() {}
        assert_send_sync::<RangeRwlock<Vec<u8>>>();
    }
}
