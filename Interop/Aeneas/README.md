# Interop / Aeneas

Bridge from [aeneas](https://github.com/AeneasVerif/aeneas)'s Lean backend
(`Aeneas.Std.Result`) to VCVio's `RustOracleComp`.

## Status

Scaffolded and **disabled pending bridge revalidation**. Upstream's published
`nightly-2026.07.11-15b9684` (commit
`15b968482b0dcd7aae45020b6d1bca39b5024af5`) natively pins Lean and Mathlib
v4.31.0, which resolves the former upstream-version blocker. The dormant pin
is recorded in `lakefile.lean`, but Aeneas remains outside dependency
resolution and CI until this bridge builds without compatibility aliases.

For history, the previous `ba600392` experiment against Lean 4.29 failed in
three places:

1. `Aeneas/Std/Primitives.lean:168:44` — kernel type mismatch in
   `CCPO (Result α) := inferInstanceAs (CCPO (FlatOrder .div))`. The
   `FlatOrder` / `CCPO` / `chain` / `is_sup` API changed between v4.28
   and v4.29. `Result α` itself still parses, but its `CCPO`/`MonoBind`
   instances do not elaborate, so we cannot import `Aeneas.Std.Primitives`
   at all.
2. `Aeneas/Tactic/Simproc/ReduceZMod/ReduceZMod.lean:83:10` —
   `Unknown constant Monoid.toNatPow` (renamed/removed in Mathlib v4.29).
3. `Aeneas/Tactic/Simp/RingEqNF/Tests.lean:113:11` — `ring_nf` leaves a
   different normal form under Mathlib v4.29, so a test's `exact h`
   mismatches. Tests only, not the main library.

Build coverage on that historical compatibility attempt was 1625/1662 jobs.

## Plan (applies once upstream ships a v4.29 build)

```lean
import Aeneas.Std.Primitives
import Interop.Rust.Common

namespace Interop.Aeneas

/-- Convert an aeneas `Result` to the equivalent `Interop.Rust.Error`-based
    `RustOracleComp`. The mapping is determined by the inductive cases:
    `ok v → RustOracleComp.pure v`,
    `fail e → RustOracleComp.fail (errorOfAeneas e)`,
    `div   → RustOracleComp.div`. -/
def errorOfAeneas : Aeneas.Std.Error → Interop.Rust.Error := ...

def ofResult {ι : Type} {spec : OracleSpec ι} {α : Type}
    (r : Aeneas.Std.Result α) : Interop.Rust.RustOracleComp spec α :=
  match r with
  | .ok v   => pure v
  | .fail e => Interop.Rust.RustOracleComp.fail (errorOfAeneas e)
  | .div    => Interop.Rust.RustOracleComp.div

instance {ι : Type} {spec : OracleSpec ι} :
    MonadLift Aeneas.Std.Result (Interop.Rust.RustOracleComp spec) where
  monadLift := ofResult
```

Plus a boundary lemma showing that the aeneas WP shape (`.except Error .pure`)
maps into VCVio's via the lift.

## Risks

- `Aeneas.Std.Error` and `Hax.Error` are nominally distinct but structurally
  identical. We mirror the shared shape as `Interop.Rust.Error` and convert
  on lift.
- Aeneas's `Result` is an inductive (not a transformer), so its
  `Std.Do.WP` instance is bespoke. Lifting goes through pattern matching,
  not transformer composition.
- The `@[step]` and `step!` tactic infrastructure cannot be re-used; VCVio's
  `mvcgen` must drive proofs on the VCVio side.
- See `docs/agents/interop.md` for the full risk list.
