# Interop / Hax

Examples of hax-extracted Rust carried into VCVio. hax now emits code in Aeneas's `RustM`, which
`Interop.Rust.liftRustM` lifts into `RustOracleComp`, so these examples need no hax-specific
bridge.

| Module | Shows | State |
|---|---|---|
| `CenteredBinomial` | ML-KEM's CBD(η = 1) step from `third_party/hax-cbd`, through `RustM`, to its exact distribution | ported; built by `InteropRust` |
| `Computation` | hax's `x + x + 1`, the first real hax source | not yet ported |
| `Division` | checked `/`: division by zero end to end | not yet ported |
| `Adc` | 32-bit add-with-carry, by `hax_mvcgen` and `bv_decide`, transported by `triple_liftRustM` | not yet ported; needs the triple transport |
| `Barrett` | signed 32-bit Barrett reduction mod 3329, in range by `hax_bv_decide` | not yet ported; needs the triple transport |
| `Examples` | hand-written demos: an oracle composed with a Rust addition, and a coin-tossed panic with probability `1/2` | not yet ported |

The unported modules still use hax's pre-Aeneas API (`Hax.rust_primitives.*`, `RustM` as
`ExceptT Error Option`, and the removed `Interop.Hax.Bridge`) and VCVio's retired `Pr[…]`
notation.
- *Porting one:* rewrite its code as a module over Aeneas's scalars, prove the statements against
  `Interop.Rust.RustM` and current VCVio, and add it to `InteropRust`'s roots in
  `Interop/lakefile.toml` and to the axiom-sweep step of CI's `Interop Bridges` job.
- *History:* their earlier design notes are in git history.
