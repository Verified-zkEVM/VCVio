# Interop / Hax

Examples of hax-extracted Rust carried into VCVio. hax now emits code in Aeneas's `RustM`, which
`Interop.Rust.liftRustM` lifts into `RustOracleComp`, so these examples need no hax-specific
bridge.

Each is transcribed in the `RustM` code hax emits today, over Aeneas's scalars (`U32`, `I32`,
literals such as `1#u8`): bitwise operations and casts are pure, while arithmetic and shifts are
checked. The hax CLI was not run to produce them. A specification proved with hax's `hax_mvcgen`
is a `Std.Do` triple, which reaches VCVio's program logic through
`Interop.Rust.triple_liftRustM_of_triple`. All are roots of `InteropRust` and of the axiom-sweep
step of CI's `Interop Bridges` job.

| Module | Shows |
|---|---|
| `CenteredBinomial` | ML-KEM's CBD(η = 1) step from `third_party/hax-cbd`, through `RustM`, to its exact distribution, and its possible values by core's `vcgen` |
| `Barrett` | ML-KEM's signed Barrett reduction modulo 3329: the result is reduced and congruent to the input, by `hax_mvcgen` and `scalar_tac` |
| `Adc` | 32-bit add-with-carry, the multi-precision building block, by `hax_mvcgen` and `scalar_tac` |
| `Computation` | `x + x + 1` from hax's Lean test suite, without overflow |
| `Division` | checked `/`: the quotient for a nonzero divisor, a panic for zero, and a panic probability of `1/2` under a uniform bit |
| `Examples` | a Rust addition after an oracle query, specified over every possible answer |
