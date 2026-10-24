/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.ProgramLogic.Library.T3.GPVHashAndSign.EmbedIndex

/-!
# Tests for the GPV signed-set index-embedding handler specifications

Core `vcgen` with the rules of `VCVio.ProgramLogic.Library.T3.GPVHashAndSign.EmbedIndex`: index
and signed-set recording along a sign-then-read program, the frame of an opaque adversary, and
a lockstep invariant of every run.
-/

public section

namespace VCVioTest.ProgramLogic.Library.T3.GPVEmbedIndex

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

/-- Signing records the counter at the signed point, signs the message, and the read of the
signed point is a hit returning a target of which the signature is a trapdoor preimage. -/
example (j : ℕ) (y : Range) (msg : M) (k : ℕ) :
    ⦃ fun s => s.1.1.2 = k ⦄
      simulateQ (embedTrapIdxSigImpl psf M Salt pk sk j y) (signRead M Salt msg)
    ⦃ fun z s => s.1.1.2 = k + 1 ∧ s.1.2 (z.1.1, msg) = some k ∧ msg ∈ s.2 ∧
        z.1.2 ∈ support (psf.trapdoorSample pk sk z.2) ⦄ := by
  vcgen
  grind

/-- An opaque inline-fresh adversary keeps every signed message and recorded index. -/
example {α : Type} (msg : M) (t : Salt × M)
    (adv : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) α) :
    ⦃ fun s => msg ∈ s.2 ∧ (s.1.2 t).isSome ⦄
      simulateQ (embedTrapFreshIdxSigImpl psf M Salt pk sk) adv
    ⦃ fun _ s => msg ∈ s.2 ∧ (s.1.2 t).isSome ⦄ := by
  vcgen
  grind

/-- `embedTrapIdxSigImpl_run_step_count_le`, re-proved by the instance frame. -/
example (j : ℕ) (y : Range)
    (t : ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))).Domain)
    (s : (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M) (z)
    (hz : z ∈ support ((embedTrapIdxSigImpl psf M Salt pk sk j y t).run s)) :
    s.1.1.2 ≤ z.2.1.1.2 :=
  ((monotoneState_embedTrapIdxSigImpl psf M Salt pk sk j y).step t s z hz).1.2

/-- The cache and the index table have the same keys throughout every run. -/
example {β : Type} (oa : OracleComp ((unifSpec + (Salt × M →ₒ Range)) + (M →ₒ (Salt × Domain))) β)
    (s : (((Salt × M →ₒ Range).QueryCache × ℕ) × ((Salt × M) → Option ℕ)) × Finset M)
    (hs : ∀ k, s.1.1.1 k ≠ none ↔ s.1.2 k ≠ none) :
    ∀ z ∈ support ((simulateQ (embedTrapFreshIdxSigImpl psf M Salt pk sk) oa).run s),
      ∀ k, z.2.1.1.1 k ≠ none ↔ z.2.1.2 k ≠ none :=
  fun _ hz => inv_of_mem_support_simulateQ_run (Inv := fun s => ∀ k, s.1.1.1 k ≠ none ↔
    s.1.2 k ≠ none) (fun t s hs ⟨_, _⟩ hz => by
      rcases t with (n | q) | msg <;> simp only [simulateQ_nf] at hz <;> grind) hs hz

end VCVioTest.ProgramLogic.Library.T3.GPVEmbedIndex
