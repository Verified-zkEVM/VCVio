//! A checked addition on `u32`, which the Lean example runs after an oracle query. Rust has no
//! oracle, so the query stays on the Lean side.
#![no_std]

use hax_lib::int::*;

#[hax_lib::requires(x <= u32::MAX - y)]
#[hax_lib::ensures(|result| result.to_int() == x.to_int() + y.to_int())]
pub fn add_or_panic(x: u32, y: u32) -> u32 {
    x + y
}
