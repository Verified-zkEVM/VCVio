/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.ProgramLogic.Library.T3.GPVHashAndSign.FlagHandlers
public import VCVio.ProgramLogic.Library.T3.GPVHashAndSign.GameRuns

/-!
# Tests for the GPV flag-instrumented handler specifications

Core `vcgen` with the rules of `VCVio.ProgramLogic.Library.T3.GPVHashAndSign.FlagHandlers`, whose
non-signing rules hand over to the `gpvRealImpl` and `progGameRunImplNoRec` rules of
`VCVio.ProgramLogic.Library.T3.GPVHashAndSign.GameRuns`.
-/

public section

namespace VCVioTest.ProgramLogic.Library.T3.GPVFlagHandlers

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

/-- The flag handler's read hands over to the real handler's rule: the read returns the cached
signing target, and the flag is never lowered. -/
example (msg : M) :
    ⦃ fun s => s.2 = true ∧ True ⦄
      simulateQ (gpvRealImplFlag psf hr M Salt pk sk) (signRead M Salt msg)
    ⦃ fun z s => s.1 (z.1.1, msg) = some z.2 ∧ s.2 = true ⦄ := by
  vcgen
  grind

/-- From the empty cache, a first signing query raises no collision flag. -/
example (msg : M) :
    ⦃ fun s => s = (∅, false) ⦄
      gpvRealImplFlag psf hr M Salt pk sk (.inr msg)
    ⦃ fun _ s => s.2 = false ⦄ := by
  vcgen
  rename_i h _ _ _ _ _
  simp [h, saltKeyed]

/-- An opaque flag-handler adversary never lowers the flag. -/
example {α : Type}
    (adv : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) α) :
    ⦃ fun s => s.2 = true ∧ True ⦄ simulateQ (gpvRealImplFlag psf hr M Salt pk sk) adv
    ⦃ fun _ s => s.2 = true ⦄ := by
  vcgen
  grind

/-- After an opaque fresh-flag adversary and a signing query, the message is signed and every
earlier signed message is kept. -/
example {α : Type} (adv : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) α)
    (msg msg' : M) :
    ⦃ fun s => msg' ∈ s.1.2 ∧ True ⦄
      (do let _ ← simulateQ (gpvRealImplFlagFresh psf hr M Salt pk sk) adv
          gpvRealImplFlagFresh psf hr M Salt pk sk (.inr msg) :
        StateT (((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) ProbComp _)
    ⦃ fun _ s => msg ∈ s.1.2 ∧ msg' ∈ s.1.2 ⦄ := by
  vcgen
  grind

/-- The programmed fresh flag handler programs the signed point to the image of the simulated
signature, which a later read returns. -/
example (msg : M) :
    ⦃ fun _ => True ⦄
      simulateQ (progGameRunImplNoRecFlagFresh psf M Salt domainSample pk) (signRead M Salt msg)
    ⦃ fun z s => z.2 = psf.eval pk z.1.2 ∧ msg ∈ s.1.2 ⦄ := by
  vcgen
  grind

/-- The flag-free fresh handler: a signing query in a simulated program, then a uniform query. -/
example (msg : M) (n : ℕ) :
    ⦃ fun _ => True ⦄
      simulateQ (gpvRealImplFresh psf hr M Salt pk sk) (do
        let σ ← query (spec := (unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain)))
          (.inr msg)
        let _ ← query (spec := (unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain)))
          (.inl (.inl n))
        return σ)
    ⦃ fun σ s => (s.1 (σ.1, msg)).isSome ∧ msg ∈ s.2 ⦄ := by
  vcgen
  grind

/-- `gpvRealImplFlag_bad_mono` is the instance frame. -/
example (t : ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Domain)
    (s : (Salt × M →ₒ Range).QueryCache × Bool) (hs : s.2 = true) :
    ∀ z ∈ support ((gpvRealImplFlag psf hr M Salt pk sk t).run s), z.2.2 = true :=
  fun z hz => ((monotoneState_gpvRealImplFlag psf M Salt hr pk sk).step t s z hz).2 hs

end VCVioTest.ProgramLogic.Library.T3.GPVFlagHandlers
