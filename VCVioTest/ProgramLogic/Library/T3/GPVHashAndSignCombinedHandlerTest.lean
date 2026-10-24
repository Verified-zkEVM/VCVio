/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.ProgramLogic.Library.T3.GPVHashAndSign.CombinedHandler
public import VCVio.ProgramLogic.Library.T3.GPVHashAndSign.GameRuns

/-!
# Tests for the GPV combined and embedding handler specifications

Core `vcgen` with the rules of `VCVio.ProgramLogic.Library.T3.GPVHashAndSign.CombinedHandler`:
programmed sign-then-read consistency, winner-slot embedding, an invariant of every combined run,
and the counter frame.
-/

public section

namespace VCVioTest.ProgramLogic.Library.T3.GPVCombinedHandler

open OracleSpec OracleComp OracleComp.ProgramLogic Std.WP GPVHashAndSign

open scoped OracleComp.Necessary

set_option experimental.vcgen true

variable {PK SK Domain Range : Type} [SampleableType Range]
  (psf : PreimageSampleableFunction PK SK Domain Range) (M Salt : Type) [DecidableEq M]
  [DecidableEq Salt] [SampleableType Salt] (pk : PK) (sk : SK)
  (domainSample : PK → ProbComp Domain)

/-- A signing query followed by a read of the signed point. -/
abbrev signRead (msg : M) :
    OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain)))
      ((Salt × Domain) × Range) := do
  let σ ← query (spec := (unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) (.inr msg)
  let v ← query (spec := (unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain)))
    (.inl (.inr (σ.1, msg)))
  return (σ, v)

/-- The combined handler answers the read of a signed point with the programmed image, and
records the simulated signature in its hidden table. -/
example (msg : M) :
    ⦃ fun _ => True ⦄
      simulateQ (progGameRunImplCombined psf M Salt domainSample pk) (signRead M Salt msg)
    ⦃ fun z s => z.2 = psf.eval pk z.1.2 ∧ s.2 (z.1.1, msg) = some z.1.2 ∧ msg ∈ s.1.1.2 ⦄ := by
  vcgen
  grind

/-- Cache/table coherence holds throughout every combined run (`progGameRunImplCombined_run_inv`
as a triple). -/
example {α : Type}
    (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) α) :
    ⦃ fun s => combinedCacheTableInv psf M Salt pk s ⦄
      simulateQ (progGameRunImplCombined psf M Salt domainSample pk) oa
    ⦃ fun _ s => combinedCacheTableInv psf M Salt pk s ⦄ := by
  refine triple_simulateQ_inv (fun t => ?_) oa
  rcases t with (n | q) | msg <;> vcgen <;> grind [combinedCacheTableInv]

/-- At the winner index a missed read of the embedding handler answers and caches the target. -/
example (w : ℕ) (y : Range) (q : Salt × M) :
    ⦃ fun s => s.2 = w ∧ s.1 q = none ⦄
      embedTrapImpl psf M Salt pk sk w y (.inl (.inr q))
    ⦃ fun v s => s.1 q = some v ∧ s.1 q = some y ∧ s.2 = w + 1 ⦄ := by
  vcgen
  rename_i h v s' hv
  rcases hv with ⟨h', -⟩ | ⟨-, hv, rfl⟩ <;> simp_all

/-- `embedTrapImpl_run_step_count_le` is the instance frame. -/
example (j : ℕ) (y : Range) (t : ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Domain)
    (s : (Salt × M →ₒ Range).QueryCache × ℕ) (z)
    (hz : z ∈ support ((embedTrapImpl psf M Salt pk sk j y t).run s)) : s.2 ≤ z.2.2 :=
  ((monotoneState_embedTrapImpl psf M Salt pk sk j y).step t s z hz).2

/-- An opaque embedding adversary followed by a signing query: the counter grows by at least one,
and every cached key stays cached. -/
example {α : Type} (j : ℕ) (y : Range) (msg : M) (t : Salt × M) (k : ℕ)
    (adv : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) α) :
    ⦃ fun s => k ≤ s.2 ∧ (s.1 t).isSome ⦄
      (do let _ ← simulateQ (embedTrapImpl psf M Salt pk sk j y) adv
          embedTrapImpl psf M Salt pk sk j y (.inr msg) :
        StateT ((Salt × M →ₒ Range).QueryCache × ℕ) ProbComp _)
    ⦃ fun _ s => k + 1 ≤ s.2 ∧ (s.1 t).isSome ⦄ := by
  vcgen
  grind [isSome_cacheQuery]

/-- The trapdoor-recording handler records a trapdoor preimage of each signing target. -/
example (msg : M) :
    ⦃ fun _ => True ⦄
      simulateQ (progGameRunImplCombinedTrap psf M Salt pk sk) (signRead M Salt msg)
    ⦃ fun z s => z.1.2 ∈ support (psf.trapdoorSample pk sk z.2) ∧
        s.2 (z.1.1, msg) = some z.1.2 ⦄ := by
  vcgen
  grind

/-- `simulateQ_nf` reads the reduction's table write off a reachable signing step. -/
example (msg : M) (s s' : (Salt × M →ₒ Range).QueryCache × ((Salt × M) → Option Domain))
    (σ : ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Range (.inr msg))
    (hz : (σ, s') ∈ support ((simulateQ (reductionImpl psf M Salt domainSample pk)
      (query (spec := (unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain)))
        (.inr msg))).run s)) :
    s'.2 (σ.1, msg) = some σ.2 := by
  simp only [simulateQ_nf] at hz
  simp [hz.2]

end VCVioTest.ProgramLogic.Library.T3.GPVCombinedHandler
