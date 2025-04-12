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

use criterion::{black_box, Criterion};
use rangelock::RangeMap;
use std::ops::Range;

pub fn bench_increment(c: &mut Criterion) {
    c.bench_function("increment 1000 random ranges", |b| {
        b.iter(|| {
            let mut map = RangeMap::new();
            for i in 0..1000 {
                let base = (i * 7) % 1000;
                map.increment(black_box(base..(base + 20)));
            }
        });
    });
}

pub fn bench_decrement(c: &mut Criterion) {
    c.bench_function("increment + decrement 1000 ranges", |b| {
        b.iter(|| {
            let mut map = RangeMap::new();
            for i in 0..1000 {
                let base = (i * 7) % 1000;
                map.increment(base..(base + 20));
            }
            for i in 0..1000 {
                let base = (i * 7) % 1000;
                map.decrement(base..(base + 20));
            }
        });
    });
}

pub fn bench_dense_inserts(c: &mut Criterion) {
    c.bench_function("dense overlapping inserts", |b| {
        b.iter(|| {
            let mut map = RangeMap::new();
            for _ in 0..500 {
                map.increment(black_box(0..1000));
            }
        });
    });
}

pub fn bench_sparse_inserts(c: &mut Criterion) {
    c.bench_function("sparse inserts", |b| {
        b.iter(|| {
            let mut map = RangeMap::new();
            for i in 0..1000 {
                map.increment(black_box((i * 100)..(i * 100 + 10)));
            }
        });
    });
}

pub fn bench_combined_ops(c: &mut Criterion) {
    c.bench_function("mixed inserts and deletes", |b| {
        b.iter(|| {
            let mut map = RangeMap::new();
            for i in 0..1000 {
                let r: Range<usize> = (i * 10)..(i * 10 + 30);
                map.increment(r.clone());
                if i % 2 == 0 {
                    map.decrement(r);
                }
            }
        });
    });
}

