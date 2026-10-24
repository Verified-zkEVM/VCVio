/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.ProgramLogic.Library.T3.GPVHashAndSign.GameRuns

/-!
# Tests for the GPV game-run handler specifications

Core `vcgen` with the rules of `VCVio.ProgramLogic.Library.T3.GPVHashAndSign.GameRuns`:
sign-then-read programs under the real, programmed and tape handlers, frames of an opaque
adversary, and support facts.
-/

public section

namespace VCVioTest.ProgramLogic.Library.T3.GPVGameRuns

open OracleSpec OracleComp OracleComp.ProgramLogic Std.WP GPVHashAndSign

open scoped OracleComp.Necessary

set_option experimental.vcgen true

variable {PK SK Domain Range : Type} {p : PK → SK → Bool} [DecidableEq Range]
  [SampleableType Range] (psf : PreimageSampleableFunction PK SK Domain Range)
  (hr : GenerableRelation PK SK p) (M Salt : Type) [DecidableEq M] [DecidableEq Salt]
  [SampleableType Salt] (pk : PK) (sk : SK) (domainSample : PK → ProbComp Domain)

/-- A signing query followed by a read of the signed point. -/
abbrev signRead (msg : M) :
    OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain)))
      ((Salt × Domain) × Range) := do
  let σ ← query (spec := (unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) (.inr msg)
  let v ← query (spec := (unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain)))
    (.inl (.inr (σ.1, msg)))
  return (σ, v)

/-- Real handler: the read returns the cached signing target, of which the signature is a
trapdoor preimage. -/
example (msg : M) :
    ⦃ fun _ => True ⦄ simulateQ (gpvRealImpl psf hr M Salt pk sk) (signRead M Salt msg)
    ⦃ fun z c => c (z.1.1, msg) = some z.2 ∧ z.1.2 ∈ support (psf.trapdoorSample pk sk z.2) ⦄ := by
  vcgen
  grind

/-- Programmed handler: the read returns the image of the simulated signature. -/
example (msg : M) :
    ⦃ fun _ => True ⦄
      simulateQ (progGameRunImplNoRec psf M Salt domainSample pk) (signRead M Salt msg)
    ⦃ fun z _ => z.2 = psf.eval pk z.1.2 ∧ z.1.2 ∈ support (domainSample pk) ⦄ := by
  vcgen
  grind

/-- An opaque real-handler adversary keeps every cached answer, so a later read returns it. The
post compares the answer through the cache: an equation `v = u` with `u : Range` would type the
triple at `Range` instead of the sum's answer type, which `vcgen` does not match. -/
example {α : Type} (adv : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) α)
    (t : Salt × M) (u : Range) :
    ⦃ fun c => c t = some u ⦄
      (do let _ ← simulateQ (gpvRealImpl psf hr M Salt pk sk) adv
          gpvRealImpl psf hr M Salt pk sk (.inl (.inr t)) :
        StateT (Salt × M →ₒ Range).QueryCache ProbComp _)
    ⦃ fun v c => c t = some v ∧ c t = some u ⦄ := by
  vcgen
  grind

/-- An opaque programmed adversary never uncaches a key. -/
example {α : Type} (adv : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) α)
    (t : Salt × M) :
    ⦃ fun c => (c t).isSome ∧ True ⦄
      simulateQ (progGameRunImplNoRec psf M Salt domainSample pk) adv
    ⦃ fun _ c => (c t).isSome ⦄ := by
  vcgen
  grind

/-- Two signing queries of the real tape handler consume the two head salts in order. -/
example (m₁ m₂ : M) (r₁ r₂ : Salt) (tl : List Salt) :
    ⦃ fun s => s.2 = r₁ :: r₂ :: tl ⦄
      (do
        let σ₁ ← gpvRealImplTape psf M Salt pk sk (.inr m₁)
        let σ₂ ← gpvRealImplTape psf M Salt pk sk (.inr m₂)
        return (σ₁, σ₂) : StateT ((Salt × M →ₒ Range).QueryCache × List Salt) ProbComp _)
    ⦃ fun z s => z.1.1 = r₁ ∧ z.2.1 = r₂ ∧ s.2 = tl ⦄ := by
  vcgen
  grind

/-- The programmed tape handler programs the consumed head salt. -/
example (msg : M) (r : Salt) (tl : List Salt) :
    ⦃ fun s => s.2 = r :: tl ⦄
      simulateQ (progGameRunImplTape psf M Salt domainSample pk) (signRead M Salt msg)
    ⦃ fun z s => z.1.1 = r ∧ z.2 = psf.eval pk z.1.2 ∧ s.2 = tl ⦄ := by
  vcgen
  grind

/-- For any program, a tape run only consumes its tape. -/
example {α : Type} (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) α)
    (s : (Salt × M →ₒ Range).QueryCache × List Salt) :
    ∀ z ∈ support ((simulateQ (gpvRealImplTape psf M Salt pk sk) oa).run s),
      s.1 ≤ z.2.1 ∧ z.2.2 <:+ s.2 :=
  fun _ hz => QueryImpl.MonotoneState.rel_of_mem_support hz

/-- `simulateQ_nf` reads a reachable programmed signing step off its support. -/
example (msg : M) (c c' : (Salt × M →ₒ Range).QueryCache)
    (σ : ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Range (.inr msg))
    (hz : (σ, c') ∈ support ((simulateQ (progGameRunImplNoRec psf M Salt domainSample pk)
      (query (spec := (unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain)))
        (.inr msg))).run c)) :
    c' (σ.1, msg) = some (psf.eval pk σ.2) := by
  simp only [simulateQ_nf] at hz
  simp [hz.2]

end VCVioTest.ProgramLogic.Library.T3.GPVGameRuns
