# Interop / Hax

Rust programs extracted by the hax CLI and carried into VCVio. hax emits code in Aeneas's `RustM`,
which `Interop.Rust.liftRustM` lifts into `RustOracleComp`, so these examples need no hax-specific
bridge.

## Layout

Each example is one directory, `Interop/Hax/<Name>/`, holding three things:

| Path | What | Written by |
|---|---|---|
| `Cargo.toml`, `hax.toml`, `src/lib.rs` | the Rust crate, with its `#[requires]` and `#[ensures]` contract | hand (Adc and Barrett are vendored from hax's examples, with provenance) |
| `Extraction/` | the Lean modules `Interop.Hax.<Name>.Extraction.{Types,Funs,Specs}`: the function, its `requires` and `ensures` clauses as `f.pre` and `f.post`, and its contract `f.spec` | `scripts/regenerate-hax.sh`, committed |
| `Verification.lean` | the proofs: the contract, its clauses in plain arithmetic, and the lifted VCVio triple | hand |

`Interop/Hax/Cargo.toml` is the workspace. It pins `hax-lib` to the hax release that
`Interop/lakefile.toml` requires. `Extraction/FunsExternal.lean` and `TypesExternal.lean` model
external definitions; they are seeded once from hax's templates, and none of the examples has any.

## Regenerating

`scripts/regenerate-hax.sh` extracts every crate with `cargo-hax`, which must be the pinned release:

```
cargo install --locked --git https://github.com/cryspen/hax --rev <rev in Interop/lakefile.toml> cargo-hax
scripts/regenerate-hax.sh          # regenerate in place
scripts/regenerate-hax.sh --check  # compare a fresh extraction with the committed modules
```

The extracted modules are committed, so building `Interop/` needs no Rust. CI's `hax Extraction`
workflow runs `--check` whenever a crate, an extracted module, the pin or the script changes. The
extracted modules form the library `InteropHaxExtraction`, built without the header linter,
because aeneas writes no module docstring.

## Proving a contract

`f.spec x` is `(f.pre x).holds → ⦃⌜True⌝⦄ f x ⦃⇓r => ⌜(f.post x r).holds⌝⦄`.
- **The contract.** It is proved with hax's `hax_mvcgen`, as hax's own proof obligations are.
- **The clauses in plain arithmetic.** `Interop.Hax.holds_ok` reads a returned Boolean as the
  Boolean itself. Where a clause calls a checked operation, `Interop.Hax.holds_iff_of_triple`
  reads it through a `hax_mvcgen` triple instead.
- **The lifted triple.** `Interop.Rust.triple_liftRustM_of_imp` turns the contract into a core
  `Std.WP` triple for the lifted program, under any `Prop`-valued interpretation of `OracleComp`.

| Example | Shows |
|---|---|
| `CenteredBinomial` | ML-KEM's CBD(η = 1) step: its contract that the result is `-1`, `0` or `1`, its exact distribution, and its possible values by core's `vcgen` |
| `Barrett` | ML-KEM's signed Barrett reduction modulo 3329: the result is reduced and congruent to the input, by hax's own proof |
| `Adc` | 32-bit add-with-carry, the multi-precision building block, by hax's own proof |
| `Computation` | `x + x + 1` from hax's Lean test suite, without overflow |
| `Division` | checked `/`: the quotient for a nonzero divisor, a panic for zero, and a panic probability of `1/2` under a uniform bit |
| `Examples` | a Rust addition after an oracle query, specified over every possible answer |

All of `Verification.lean` and `Interop.Hax.Holds` are roots of `InteropRust` and of the axiom-sweep
step of CI's `Interop Bridges` job.
