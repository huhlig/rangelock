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
use rangelock::{AsSlice, RangeMutex};
use std::sync::Arc;
use std::thread;

pub fn bench_range_mutex(c: &mut Criterion) {
    let mut group = c.benchmark_group("RangeMutex");

    // Benchmark single-threaded range locking
    group.bench_function("single_range_lock", |b| {
        let mutex = RangeMutex::new(vec![0u8; 1000]);
        b.iter(|| {
            let mut guard = mutex.try_range(0..100).unwrap();
            black_box(guard.as_mut().iter_mut().for_each(|x| *x = 1));
        });
    });

    // Benchmark non-overlapping concurrent ranges
    group.bench_function("concurrent_non_overlapping", |b| {
        b.iter(|| {
            let mutex = Arc::new(RangeMutex::new(vec![0u8; 1000]));
            let mut handles = Vec::new();

            for i in 0..5 {
                let mutex = Arc::clone(&mutex);
                let handle = thread::spawn(move || {
                    let start = i * 200;
                    let end = start + 200;
                    let mut guard = mutex.try_range(start..end).unwrap();
                    guard.as_mut().iter_mut().for_each(|x| *x = 1);
                });
                handles.push(handle);
            }

            for handle in handles {
                handle.join().unwrap();
            }
        });
    });

    // Benchmark different range sizes
    for size in [10, 100, 1000].iter() {
        group.bench_with_input(BenchmarkId::new("range_size", size), size, |b, &size| {
            let mutex = RangeMutex::new(vec![0u8; size * 2]);
            b.iter(|| {
                let mut guard = mutex.try_range(0..size).unwrap();
                black_box(guard.as_mut().iter_mut().for_each(|x| *x = 1));
            });
        });
    }

    // Benchmark full mutex lock
    group.bench_function("full_mutex_lock", |b| {
        let mutex = RangeMutex::new(vec![0u8; 1000]);
        b.iter(|| {
            let mut guard = mutex.try_mutex().unwrap();
            black_box(guard.as_slice_mut().iter_mut().for_each(|x| *x = 1));
        });
    });

    // Benchmark contention scenario
    group.bench_function("lock_contention", |b| {
        b.iter(|| {
            let mutex = Arc::new(RangeMutex::new(vec![0u8; 100]));
            let mut handles = Vec::new();

            for _ in 0..4 {
                let mutex = Arc::clone(&mutex);
                let handle = thread::spawn(move || {
                    for i in 0..25 {
                        let mut guard = mutex.try_range(i..i + 1).unwrap();
                        *guard.as_mut().get_mut(0).unwrap() = 1;
                    }
                });
                handles.push(handle);
            }

            for handle in handles {
                handle.join().unwrap();
            }
        });
    });

    group.finish();
}
