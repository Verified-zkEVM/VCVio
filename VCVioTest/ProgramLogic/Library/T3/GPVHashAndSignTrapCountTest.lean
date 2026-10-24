/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.ProgramLogic.Library.T3.GPVHashAndSign.TrapCount

/-!
# Tests for the GPV counting and index-embedding handler specifications

Core `vcgen` with the rules of `VCVio.ProgramLogic.Library.T3.GPVHashAndSign.TrapCount`: index
recording along a sign-then-read program, lockstep invariants of every run (two existing
inductions re-proved in three lines), and the counter frame.
-/

public section

namespace VCVioTest.ProgramLogic.Library.T3.GPVTrapCount

open OracleSpec OracleComp OracleComp.ProgramLogic Std.WP GPVHashAndSign

open scoped OracleComp.Necessary

set_option experimental.vcgen true

variable {PK SK Domain Range : Type} [SampleableType Range]
  (psf : PreimageSampleableFunction PK SK Domain Range) (M Salt : Type) [DecidableEq M]
  [DecidableEq Salt] [SampleableType Salt] (pk : PK) (sk : SK)

/-- A signing query followed by a read of the signed point. -/
abbrev signRead (msg : M) :
    OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain)))
      ((Salt × Domain) × Range) := do
  let σ ← query (spec := (unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) (.inr msg)
  let v ← query (spec := (unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain)))
    (.inl (.inr (σ.1, msg)))
  return (σ, v)

/-- The counting trap run records the counter at the signed point and advances it once: the
read of the signed point is a hit. -/
example (msg : M) (k : ℕ) :
    ⦃ fun s => s.2.2 = k ⦄
      simulateQ (progGameRunImplCombinedTrapCount psf M Salt pk sk) (signRead M Salt msg)
    ⦃ fun z s => s.2.2 = k + 1 ∧ s.2.1 (z.1.1, msg) = some k ∧
        z.1.2 ∈ support (psf.trapdoorSample pk sk z.2) ⦄ := by
  vcgen
  grind

/-- `progGameRunImplCombinedTrapCount_idx_iff_table`, re-proved: the preimage table and the
index table have the same keys throughout every run. -/
example {β : Type} (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) β)
    (s : ((((Salt × M →ₒ Range).QueryCache × Finset M) × Bool) × ((Salt × M) → Option Domain)) ×
      (((Salt × M) → Option ℕ) × ℕ)) (hs : ∀ k, s.1.2 k ≠ none ↔ s.2.1 k ≠ none) :
    ∀ z ∈ support ((simulateQ (progGameRunImplCombinedTrapCount psf M Salt pk sk) oa).run s),
      ∀ k, z.2.1.2 k ≠ none ↔ z.2.2.1 k ≠ none :=
  fun _ hz => inv_of_mem_support_simulateQ_run
    (Inv := fun s => ∀ k, s.1.2 k ≠ none ↔ s.2.1 k ≠ none) (fun t s hs ⟨_, _⟩ hz => by
      rcases t with (n | q) | msg <;> simp only [simulateQ_nf] at hz <;> grind) hs hz

/-- `embedTrapIdxImpl_idx_iff_cache`, re-proved: the cache and the index table have the same keys
throughout every run of the index-recording embedding handler. -/
example (j : ℕ) (y : Range) {β : Type}
    (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) β)
    (s : ((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ))
    (hs : ∀ k, s.1.1 k ≠ none ↔ s.2 k ≠ none) :
    ∀ z ∈ support ((simulateQ (embedTrapIdxImpl psf M Salt pk sk j y) oa).run s),
      ∀ k, z.2.1.1 k ≠ none ↔ z.2.2 k ≠ none :=
  fun _ hz => inv_of_mem_support_simulateQ_run (Inv := fun s => ∀ k, s.1.1 k ≠ none ↔ s.2 k ≠ none)
    (fun t s hs ⟨_, _⟩ hz => by rcases t with (n | q) | msg <;> simp only [simulateQ_nf] at hz <;>
      grind) hs hz

/-- `embedTrapIdxImpl_run_step_count_le`, re-proved by the instance frame. -/
example (j : ℕ) (y : Range)
    (t : ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Domain)
    (s : ((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) (z)
    (hz : z ∈ support ((embedTrapIdxImpl psf M Salt pk sk j y t).run s)) : s.1.2 ≤ z.2.1.2 :=
  ((monotoneState_embedTrapIdxImpl psf M Salt pk sk j y).step t s z hz).1.2

/-- An index recorded before an opaque counting adversary stays recorded, and the counter does
not decrease. -/
example {α : Type} (k : ℕ) (t : Salt × M)
    (adv : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) α) :
    ⦃ fun s => (s.2.1 t).isSome ∧ k ≤ s.2.2 ⦄
      simulateQ (progGameRunImplCombinedTrapCount psf M Salt pk sk) adv
    ⦃ fun _ s => (s.2.1 t).isSome ∧ k ≤ s.2.2 ⦄ := by
  vcgen
  grind

/-- The inline-fresh embedding handler answers a fresh read uniformly and caches it, advancing
the counter. The post compares the answer, typed at the sum's answer type, with a cache entry:
`grind` does not identify the two `some` terms, `simp_all` does. -/
example (q : Salt × M) (k : ℕ) :
    ⦃ fun s => s.1 q = none ∧ s.2 = k ⦄ embedTrapFreshImpl psf M Salt pk sk (.inl (.inr q))
    ⦃ fun v s => s.1 q = some v ∧ s.2 = k + 1 ⦄ := by
  vcgen
  simp_all

end VCVioTest.ProgramLogic.Library.T3.GPVTrapCount
