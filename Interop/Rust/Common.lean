/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import Std.Tactic.Do
public import VCVio.ProgramLogic.Unary.StdDoBridge

/-!
# `RustOracleComp`: target monad for Rust verification frontends

A monad transformer stack that is the natural target for Lean code emitted
by Rust verification frontends (currently
[hax](https://github.com/cryspen/hax) and
[aeneas](https://github.com/AeneasVerif/aeneas)) once we want oracle access:

```
RustOracleComp spec α  :=  ExceptT Error (OptionT (OracleComp spec)) α
```

The `ExceptT Error` layer models Rust panics, the `OptionT` layer models
divergence, and the `OracleComp spec` layer models probabilistic / oracle
queries.

The `Error` enum in this file covers the errors Rust frontends report. It is local, so this module
compiles without the hax or Aeneas Lake packages. hax and Aeneas both emit code in
`Aeneas.Std.RustM`, whose computations return, fail or diverge; `Interop.Rust.RustM` lifts it into
`RustOracleComp spec` by that case analysis.

## Why a transformer stack?

It is the smallest extension of a Rust frontend's target that admits oracle queries: failure is the
`ExceptT` layer, divergence the `OptionT` layer, and queries the inner `OracleComp spec`, so the
boundary lemmas of the lift are case splits.
-/

public section

open Std.Do

namespace Interop.Rust

/-- The errors a Rust frontend reports, kept locally so this module depends on no frontend's
package; `Interop.Rust.errorOfAeneas` maps Aeneas's errors into it. -/
inductive Error where
  | assertionFailure : Error
  | integerOverflow : Error
  | divisionByZero : Error
  | arrayOutOfBounds : Error
  | maximumSizeExceeded : Error
  | panic : Error
  | undef : Error
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Oracle-aware version of `Hax.RustM` / `Aeneas.Std.Result`.

`ExceptT Error (OptionT (OracleComp spec)) α` is, layer by layer:
* `OracleComp spec` for oracle access and probabilistic semantics,
* `OptionT _` for divergence (`none` ≡ `div`),
* `ExceptT Error _` for Rust panics (`some (.error e)` ≡ `fail e`).

Once a computation panics it cannot diverge, and once it diverges it
cannot return — exactly the semantics of `Hax.RustM` and `Aeneas.Std.Result`. -/
abbrev RustOracleComp {ι : Type} (spec : OracleSpec ι) (α : Type) : Type :=
  ExceptT Error (OptionT (OracleComp spec)) α

namespace RustOracleComp

variable {ι : Type} {spec : OracleSpec ι} {α : Type}

/-- A successful Rust computation. -/
@[expose, reducible, match_pattern]
def ok (v : α) : RustOracleComp spec α := pure v

/-- A panicking Rust computation. -/
@[expose, reducible, match_pattern]
def fail (e : Error) : RustOracleComp spec α := throw e

/-- A diverging Rust computation. -/
@[expose, reducible, match_pattern]
def div : RustOracleComp spec α :=
  ExceptT.mk (OptionT.mk (pure none))

/-- Lift an oracle computation into the Rust target by treating it as a
total, panic-free Rust value. This is the `pure`/`some` chain through both
transformers and is what every oracle query reduces to inside the Rust
target.

Defined as the two-step `ExceptT.lift ∘ OptionT.lift` so `mvcgen` can
peel the `MonadLiftT (OracleComp spec) (RustOracleComp spec)` chain via
the standard `@[spec]` rules `Spec.monadLift_OptionT` and
`Spec.monadLift_ExceptT`. A direct `MonadLift (OracleComp spec)
(RustOracleComp spec)` instance would short-circuit that chain and leave
mvcgen with no spec rule to apply. -/
@[expose, reducible]
def liftOracleComp (oa : OracleComp spec α) : RustOracleComp spec α :=
  ExceptT.lift (OptionT.lift oa)

end RustOracleComp

end Interop.Rust
