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

use criterion::{criterion_group, criterion_main};

mod rangemap;
mod rangemutex;
mod rangerwlock;

criterion_group!(
    rangemap,
    rangemap::bench_increment,
    rangemap::bench_decrement,
    rangemap::bench_dense_inserts,
    rangemap::bench_sparse_inserts,
    rangemap::bench_combined_ops
);
criterion_group!(rangemutex, rangemutex::bench_range_mutex);
criterion_group!(rangerwlock, rangerwlock::bench_range_rwlock);
criterion_main!(rangemap, rangemutex, rangerwlock);