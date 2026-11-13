//! # Centered Binomial Distribution (CBD, η = 1) – single coefficient
//!
//! This crate isolates the innermost step of ML-KEM's noise sampler
//! (`SamplePolyCBD_η`) at parameter `η = 1`: given one byte of
//! uniform randomness, produce a single signed field-element in
//! `{-1, 0, 1}` whose distribution is the centered binomial with
//! parameter 1.
//!
//! Formally, for a uniform byte `b ∈ {0, …, 255}`:
//!
//!   ```text
//!   a    = b        & 1          ∈ {0, 1}
//!   c    = (b >> 1) & 1          ∈ {0, 1}
//!   CBD1 = a - c                 ∈ {-1, 0, 1}
//!   ```
//!
//! The purpose of this crate in the VCVio interop layer is to
//! demonstrate a randomized hax-emitted function: on the `RustM` side
//! its contract says the output lies in `{-1, 0, 1}`, proved with
//! `hax_mvcgen`; on the `RustOracleComp` side VCVio proves the exact
//! probability that the output equals 0, +1, or −1.

#![no_std]

/// One centered-binomial coefficient at parameter η = 1.
///
/// The two low bits of `b` are treated as independent Bernoulli(1/2)
/// samples `a`, `c`; the output is `a − c`. All six higher bits of
/// `b` are unused by this function.
#[hax_lib::ensures(|result| -1 <= result && result <= 1)]
pub fn sample_cbd1(b: u8) -> i32 {
    let a = (b & 1) as i32;
    let c = ((b >> 1) & 1) as i32;
    a - c
}
