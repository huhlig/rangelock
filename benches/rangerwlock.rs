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

use criterion::{black_box, BenchmarkId, Criterion};
use rangelock::{AsSlice, RangeRwlock};
use std::sync::Arc;
use std::thread;

pub fn bench_range_rwlock(c: &mut Criterion) {
    let mut group = c.benchmark_group("RangeRwlock");

    // Benchmark single-threaded read operations
    group.bench_function("single_read", |b| {
        let rwlock = RangeRwlock::new(vec![0u8; 1000]);
        b.iter(|| {
            let guard = rwlock.try_read(0..100).unwrap();
            black_box(guard.as_ref());
        });
    });

    // Benchmark single-threaded write operations
    group.bench_function("single_write", |b| {
        let rwlock = RangeRwlock::new(vec![0u8; 1000]);
        b.iter(|| {
            let mut guard = rwlock.try_write(0..100).unwrap();
            black_box(guard.as_mut().iter_mut().for_each(|x| *x = 1));
        });
    });

    // Benchmark concurrent reads on same range
    group.bench_function("concurrent_reads_same_range", |b| {
        b.iter(|| {
            let rwlock = Arc::new(RangeRwlock::new(vec![0u8; 1000]));
            let mut handles = Vec::new();

            for _ in 0..4 {
                let rwlock = Arc::clone(&rwlock);
                let handle = thread::spawn(move || {
                    let guard = rwlock.try_read(0..100).unwrap();
                    black_box(guard.as_ref());
                });
                handles.push(handle);
            }

            for handle in handles {
                handle.join().unwrap();
            }
        });
    });

    // Benchmark concurrent reads on different ranges
    group.bench_function("concurrent_reads_different_ranges", |b| {
        b.iter(|| {
            let rwlock = Arc::new(RangeRwlock::new(vec![0u8; 1000]));
            let mut handles = Vec::new();

            for i in 0..4 {
                let rwlock = Arc::clone(&rwlock);
                let handle = thread::spawn(move || {
                    let start = i * 200;
                    let guard = rwlock.try_read(start..start + 200).unwrap();
                    black_box(guard.as_ref());
                });
                handles.push(handle);
            }

            for handle in handles {
                handle.join().unwrap();
            }
        });
    });

    // Benchmark concurrent writes on different ranges
    group.bench_function("concurrent_writes_different_ranges", |b| {
        b.iter(|| {
            let rwlock = Arc::new(RangeRwlock::new(vec![0u8; 1000]));
            let mut handles = Vec::new();

            for i in 0..4 {
                let rwlock = Arc::clone(&rwlock);
                let handle = thread::spawn(move || {
                    let start = i * 200;
                    let mut guard = rwlock.try_write(start..start + 200).unwrap();
                    guard.as_mut().iter_mut().for_each(|x| *x = 1);
                });
                handles.push(handle);
            }

            for handle in handles {
                handle.join().unwrap();
            }
        });
    });

    // Benchmark mixed read/write operations
    group.bench_function("mixed_read_write", |b| {
        b.iter(|| {
            let rwlock = Arc::new(RangeRwlock::new(vec![0u8; 1000]));
            let mut handles = Vec::new();

            // Spawn reader threads
            for i in 0..3 {
                let rwlock = Arc::clone(&rwlock);
                let handle = thread::spawn(move || {
                    let guard = rwlock.try_read(i * 200..(i + 1) * 200).unwrap();
                    black_box(guard.as_ref());
                });
                handles.push(handle);
            }

            // Spawn writer thread
            let rwlock_clone = Arc::clone(&rwlock);
            handles.push(thread::spawn(move || {
                let mut guard = rwlock_clone.try_write(600..800).unwrap();
                guard.as_mut().iter_mut().for_each(|x| *x = 1);
            }));

            for handle in handles {
                handle.join().unwrap();
            }
        });
    });

    // Benchmark different range sizes
    for size in [10, 100, 1000].iter() {
        group.bench_with_input(
            BenchmarkId::new("read_range_size", size),
            size,
            |b, &size| {
                let rwlock = RangeRwlock::new(vec![0u8; size * 2]);
                b.iter(|| {
                    let guard = rwlock.try_read(0..size).unwrap();
                    black_box(guard.as_ref());
                });
            },
        );

        group.bench_with_input(
            BenchmarkId::new("write_range_size", size),
            size,
            |b, &size| {
                let rwlock = RangeRwlock::new(vec![0u8; size * 2]);
                b.iter(|| {
                    let mut guard = rwlock.try_write(0..size).unwrap();
                    guard.as_mut().iter_mut().for_each(|x| *x = 1);
                });
            },
        );
    }

    // Benchmark full mutex operations
    group.bench_function("full_mutex", |b| {
        let rwlock = RangeRwlock::new(vec![0u8; 1000]);
        b.iter(|| {
            let mut guard = rwlock.try_mutex().unwrap();
            black_box(guard.as_slice_mut().iter_mut().for_each(|x| *x = 1));
        });
    });

    group.finish();
}
