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

//! Error types and results for the RangeLock library.

/// A specialized Result type for RangeLock operations.
pub type RangelockResult<T> = Result<T, RangelockError>;

/// Errors that can occur during RangeLock operations.
#[derive(Debug)]
pub enum RangelockError {
    /// The requested range is already locked by another operation.
    RangeAlreadyLocked,
    /// The requested range extends beyond the allocated size.
    RangeNotAllocated,
}


impl std::fmt::Display for RangelockError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            RangelockError::RangeAlreadyLocked => write!(f, "Range is already locked"),
            RangelockError::RangeNotAllocated => write!(f, "Range extends beyond allocated size"),
        }
    }
}


impl std::error::Error for RangelockError {}
