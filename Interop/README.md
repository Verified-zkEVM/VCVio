# Interop

Bridges that let VCVio reason about Lean code produced by external verification tools: today, the
Rust frontends [hax](https://github.com/cryspen/hax) and
[Aeneas](https://github.com/AeneasVerif/aeneas).

## A separate package

The Rust bridges need hax's and Aeneas's Lean libraries, and every package that requires VCVio
would resolve any `require` in VCVio's root lakefile. So `Interop/lakefile.toml` is its own Lake
package. It requires VCVio by path and hax by commit; hax brings Aeneas.
- *Sources.* It reads them from the repository root (`srcDir = ".."`), so modules keep their
  `Interop.` names.
- *Pins.* Its pins equal the root's (Lean v4.35.0, Mathlib v4.35.0), so it shares the root's
  dependency cache. A bridge with no Lake dependency of its own can build in the root package
  instead.

```bash
cd Interop
lake build      # VCVio, hax, Aeneas and the bridges (`InteropRust`)
```

CI's `Interop Bridges` job (`.github/workflows/build.yml`) builds the package on every PR and runs
the axiom sweep over `InteropRust`'s modules.

## TCB isolation

Nothing in core VCVio depends on `Interop`. A Rust frontend's trusted base (its extraction engine,
Charon, its runtime library) must never reach a routine build of the core.
- `VCVio/`, `ToMathlib/`, `LatticeCrypto/`, `LatticeCryptoTest/`, `Examples/`, `Extern/` and
  `VCVioTest/` never import `Interop.…`, `Hax.…` or `Aeneas.…`.
- `Interop/**` may import `VCVio/**`, `ToMathlib/**`, PolyFun, hax and Aeneas, but not the
  libraries that are themselves VCVio's clients.
- `scripts/check-interop-isolation.sh` checks both directions, and
  `.github/workflows/interop-isolation.yml` runs it on every PR.
- To share infrastructure between `Interop` and another library, move it into `VCVio/` first.

## The Rust bridges

hax and Aeneas emit code in one monad, `Aeneas.Std.RustM`. hax's Lean library builds on Aeneas's,
and the fork of Aeneas it pins names it `RustM`; upstream Aeneas calls the same definition
`Result`.
- It is an interaction tree over Aeneas's effect `RustEffect`, from Aeneas's own coinductive
  library.
- That effect's only event is `fail e`, with no answer. So a `RustM` computation unfolds in one step
  to a returned value, a failure or divergence, and one lift serves both tools.

| Module | Content |
|---|---|
| `Interop.Rust.Common` | `RustOracleComp spec α := ExceptT Error (OptionT (OracleComp spec)) α`: Rust panics, then divergence, then oracle queries |
| `Interop.Rust.Run` | `.run.run` equations for that stack, for probabilistic proofs |
| `Interop.Rust.RustM` | the lift `RustM → RustOracleComp spec`, with its `pure`/`bind` laws, `LawfulMonadLift` and a bundled `MonadHom` |
| `Interop.Rust.Triple` | Aeneas's specifications (`spec`, `dspec`, `Std.Do` triples) as `Std.WP` triples for the lift, under any interpretation of `OracleComp spec`, and the `vcgen` rule `Spec.liftRustM` |
| `Interop.Aeneas.ITree` | Aeneas's interaction trees as PolyFun's: an injective monad morphism into `ITree ⟨E.I, E.O⟩`, sending `div` to `ITree.diverge` |
| `Interop.Hax.CenteredBinomial` | ML-KEM's CBD(η = 1) step, from its Rust source (`third_party/hax-cbd`) through `RustM` to its distribution: `0` with probability `1/2`, `±1` with `1/4` each |

The other modules in `Interop/Hax/` predate hax's move onto Aeneas, and are not built until they
are ported; see [its README](Hax/README.md).

## Not yet done

- **Port the other hax examples** to Aeneas's scalars (`U8`, `I32`, literals such as `1#u8`), where
  bitwise operations and casts are pure and shifts and arithmetic are checked.
- **Regenerate extractions.** Regenerate `third_party/hax-cbd` with the hax CLI. The sampler in
  `CenteredBinomial` is transcribed in hax's current emission style.
- **Weakest preconditions at the tree level.** Aeneas's per-effect specifications (`EffectWP`)
  are PolyFun's `OpSpec`s, and its total and partial correctness (`DWP`, `DWLP`) are least and
  greatest fixed points over its trees. PolyFun has `wpFold` for `FreeM` but no counterpart for
  `ITree` yet. Once it does, `Interop.Aeneas.ITree` can state that `toPolyFun` carries one to the
  other, for every Aeneas effect.
