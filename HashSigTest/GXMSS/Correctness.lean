/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Completeness
public import HashSigTest.GXMSS.Chain

/-!
# Complete-construction correctness observations

A finite Boolean hash instance retains its biased public-seed draw. A half-failing encoder
separates zero-retry exhaustion from per-key and joint canonical correctness at positive budgets.
-/

public section

namespace GXMSS.CorrectnessProbe

open IncomparableEncoding ENNReal OracleComp

/-- Tagged inputs preserve the three embeddings even for one-bit hash outputs. -/
abbrev Input := Bool ⊕ ((Bool × Bool) ⊕ (Fin 1 → Bool))

/-- The actual hash seed is biased by its finite canonical draw. -/
@[expose] def seedGen : ProbComp Bool := do
  let r ← $ᵗ (Fin 3)
  return r != 0

/-- A finite output hash instance whose parameters retain the actual seed sampler. -/
@[expose] def hash (h w : ℕ) : HashInstance Bool ChainProbe.TraceTweak Input Bool h w 1 where
  thf := {
    seedGen := seedGen
    eval := fun pp _ input => match input with
      | .inl x => pp != x
      | .inr (.inl (left, right)) => left != right
      | .inr (.inr xs) => xs 0 }
  digestInput := ⟨Sum.inl, by intro a b hab; exact Sum.inl.inj hab⟩
  pairInput := ⟨fun x => .inr (.inl x), by intro a b hab; exact Sum.inl.inj (Sum.inr.inj hab)⟩
  vectorInput := ⟨fun x => .inr (.inr x), by intro a b hab; exact Sum.inr.inj (Sum.inr.inj hab)⟩
  chainTweak := ⟨fun (e, i, j) => .inl (e.val, i.val, j.val), by
    intro a b hab
    simpa only [Sum.inl.injEq, Prod.ext_iff, Fin.ext_iff] using hab⟩
  treeTweak := ⟨fun (z, i) => .inr (z.val, i.val), by
    intro a b hab
    simpa only [Sum.inr.injEq, Prod.ext_iff, Fin.ext_iff] using hab⟩
  chain_ne_tree := by
    intro c t heq
    cases c
    cases t
    cases heq


/-- False randomness returns failure; true randomness emits the singleton zero word. -/
@[expose] def enc (h : ℕ) : IncomparableEncoding Bool Unit Bool (Fin (2 ^ h)) 1 2 where
  code := {fun _ => 0}
  incomparable := by
    intro x hx y hy hne
    exact (hne ((Set.mem_singleton_iff.mp hx).trans (Set.mem_singleton_iff.mp hy).symm)).elim
  encode _ _ r _ := if r then some ⟨fun _ => 0, by simp⟩ else none

/-- One canonical attempt fails with exactly one-half returned mass at every input. -/
theorem failure_half (h : ℕ) (pp : Bool) (msg : Unit) (ep : Fin (2 ^ h)) :
    (enc h).failureMass ProbCompRuntime.probComp ($ᵗ Bool) pp msg ep = 2⁻¹ := by
  have hclass : (enc h).failed pp msg ep = fun r : Bool => !r := by
    funext r
    cases r <;> rfl
  change ProbCompRuntime.probComp.evalDist ((enc h).failed pp msg ep <$> ($ᵗ Bool)) {true} = 2⁻¹
  rw [hclass, ProbCompRuntime.probComp_evalDist, evalDist_map _ Measurable.of_discrete,
    MeasureTheory.Measure.map_apply Measurable.of_discrete (MeasurableSet.singleton true)]
  have hpre : (fun r : Bool => !r) ⁻¹' ({true} : Set Bool) = {false} := by
    ext r
    cases r <;> simp
  rw [hpre]
  simp

/-- The pointwise encoding premise samples only the randomizer, not the public seed. -/
theorem canonical_half (h : ℕ) : (enc h).CanonicalErrorAtMost (2⁻¹) := by
  intro pp msg ep
  exact le_of_eq (failure_half h pp msg ep)

/-- The same biased actual key generator satisfies the canonical total-mass statement. -/
theorem actual_keygen_lossless (h : ℕ) :
    LosslessSampler ProbCompRuntime.probComp (keygen (hash h 1)) := keygen_lossless _

/-- Every generated key has correctness error at most the exact retry power. -/
theorem per_key (h K : ℕ) :
    (scheme (hash h 1) (enc h) K).CompletePerKey ProbCompRuntime.probComp ((2⁻¹) ^ K) :=
  completePerKey _ _ K (2⁻¹) (canonical_half h)

/-- The actual joint keygen-sign-verify observation has the same correctness bound. -/
theorem joint (h K : ℕ) :
    (scheme (hash h 1) (enc h) K).Complete ProbCompRuntime.probComp ((2⁻¹) ^ K) :=
  complete _ _ K (2⁻¹) (canonical_half h)

/-- A zero retry budget returns a losing Boolean after the actual keygen computation. -/
theorem joint_zero (h : ℕ) (ep : Fin (2 ^ h)) :
    (scheme (hash h 1) (enc h) 0).correctnessExperiment ep () =
      (fun _ => false) <$> keygen (hash h 1) := by
  simp [SyncSignatureAlg.correctnessExperiment, scheme, sign_zero, SyncSignatureAlg.accepts]

/-- The zero-retry joint successful-output mass is zero after the retained keygen draw. -/
theorem joint_zero_mass (h : ℕ) (ep : Fin (2 ^ h)) :
    (scheme (hash h 1) (enc h) 0).jointSuccessMass ProbCompRuntime.probComp ep () = 0 := by
  simp [SyncSignatureAlg.jointSuccessMass, joint_zero, ProbCompRuntime.probComp_evalDist]

/-- The per-key exact mass separates returned retry exhaustion from successful verification. -/
theorem per_key_exact (h K : ℕ) (ks : PublicKey Bool Bool × SecretKey Bool Bool h 1)
    (hc : Consistent (hash h 1) ks.1 ks.2) (ep : Fin (2 ^ h)) :
    (scheme (hash h 1) (enc h) K).successMass ProbCompRuntime.probComp ks ep () =
      1 - (2⁻¹) ^ K := by
  rw [successMass_eq_one_sub_pow _ _ K ks hc]
  dsimp
  rw [failure_half]

end GXMSS.CorrectnessProbe
