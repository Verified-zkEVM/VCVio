//! `x + x + 1`, from hax's Lean test suite (`tests/src/legacy/lean-tests/constants.rs` at
//! a045d15a3bf43fe05096146f488668b521a4ae44, Apache-2.0), where it is a private `const fn`. It is
//! public here, with a contract: without overflow, the result is `2x + 1`.
#![no_std]

use hax_lib::int::*;

#[hax_lib::requires(x <= 0x7FFF_FFFF)]
#[hax_lib::ensures(|result| result.to_int() == x.to_int() * int!(2) + int!(1))]
pub fn computation(x: u32) -> u32 {
    x + x + 1
}
