# Interop/Aeneas/Hax

The hax examples of the [`Interop/Aeneas`](../README.md) sub-project, listed under its
*Implementations covered*: Rust programs extracted by the hax CLI and carried into VCVio. hax emits
code in Aeneas's `RustM`, which `Interop.Rust.liftRustM` lifts into `RustOracleComp`, so these
examples need no hax-specific bridge.

## Layout

Each example is one directory, `Interop/Aeneas/Hax/<Name>/`, holding three things:

| Path | What | Written by |
|---|---|---|
| `Cargo.toml`, `hax.toml`, `src/lib.rs` | the Rust crate, with its `#[requires]` and `#[ensures]` contract | hand (Adc and Barrett are vendored from hax's examples, with provenance) |
| `Extraction/` | the Lean modules `Interop.Aeneas.Hax.<Name>.Extraction.{Types,Funs,Specs}`: the function, its `requires` and `ensures` clauses as `f.pre` and `f.post`, and its contract `f.spec` | `scripts/regenerate-hax.sh`, committed |
| `Verification.lean` | the proofs: the contract, its clauses in plain arithmetic, and the lifted VCVio triple | hand |

`Interop/Aeneas/Hax/Cargo.toml` is the workspace. It pins `hax-lib` to the hax release that
`Interop/Aeneas/lakefile.toml` requires. `Extraction/FunsExternal.lean` and `TypesExternal.lean`
model external definitions; they are seeded once from hax's templates, and none of the examples
has any. Each crate's `hax.toml` sends the extraction to the repository root (`-dest`) under its
own path (`-subdir`), so the module names follow the paths.

## Regenerating

The regeneration script uses Python 3.11 or later to read the hax commit from the Lean and Rust
package files. Install that revision of `cargo-hax` to reproduce the extractions.

```
cargo install --locked --git https://github.com/cryspen/hax --rev "$(scripts/regenerate-hax.sh --print-pin)" cargo-hax
scripts/regenerate-hax.sh          # regenerate in place
scripts/regenerate-hax.sh --check  # compare a fresh extraction with the committed modules
```

The extracted modules are committed, so building the sub-project needs no Rust. CI's
`hax Extraction` workflow runs `--check` whenever a crate, an extracted module, the pin or the
script changes. The extracted modules form the library `InteropAeneasHaxExtraction`, built without
the header linter, because aeneas writes no module docstring.

## Proving a contract

`f.spec x` is `(f.pre x).holds → ⦃⌜True⌝⦄ f x ⦃⇓r => ⌜(f.post x r).holds⌝⦄`.
- **The contract.** It is proved with hax's `hax_mvcgen`, as hax's own proof obligations are.
- **The clauses in plain arithmetic.** `Interop.Hax.holds_ok` reads a returned Boolean as the
  Boolean itself. Where a clause calls a checked operation, `Interop.Hax.holds_iff_of_triple`
  reads it through a `hax_mvcgen` triple instead.
- **The lifted triple.** `Interop.Rust.triple_liftRustM_of_imp` turns the contract into a core
  `Std.WP` triple for the lifted program, under any `Prop`-valued interpretation of `OracleComp`.

## Adding an example

Add the crate to the workspace members in `Cargo.toml`, give it a `hax.toml` like its neighbours',
and run `scripts/regenerate-hax.sh`. In `../lakefile.toml`, add a glob for its `Extraction`
modules to the library `InteropAeneasHaxExtraction` and its `Verification` module to the roots of
`InteropAeneas`. Those roots are also the roots of the sub-project's axiom sweep in CI, and the
example gets a row under *Implementations covered* in [the sub-project's README](../README.md).
