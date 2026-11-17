//! Checked division on `u32`: Rust's `x / y` panics when `y` is zero.
#![no_std]

#[hax_lib::requires(y != 0)]
#[hax_lib::ensures(|result| result == x / y)]
pub fn checked_div(x: u32, y: u32) -> u32 {
    x / y
}
