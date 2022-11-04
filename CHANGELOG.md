# 0.1.2 (2022-11-04)

 - Add optional [`arbitrary`](https://crates.io/crates/arbitrary) integration (`arbitrary` feature)
 - Switch to Rust 2021 edition

# 0.1.1 (2022-01-23)

 - Add `guaranteed_head` and `guaranteed_tail` methods that return a fixed-size array of the minimum size with the first and last items respectively. Suggested by [Nemo157](https://github.com/Nemo157).
 - Add some diagnostic function attributes:
   - Add `#[must_use]` to `MinSizedVec::into_inner`
   - Add `#[track_caller]` to `MinSizedVec::remove` and `MinSizedVec::swap_remove`

# 0.1.0 (2021-07-30)

Initial release.
