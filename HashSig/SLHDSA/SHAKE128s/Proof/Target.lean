/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.MainTheorem
public import HashSig.SLHDSA.SHAKE128s.Proof.WalkDefects
public import HashSig.SLHDSA.SHAKE128s.Proof.Experiment
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import HashSig.SLHDSA.SHAKE128s.Proof.HonestGrowth

/-!
# The walk and the game together

This file fixes how the walk's own randomness enters the whole-game bound. The walk draws the
seeds and the cell table before any adversary exists. A walk whose seeds coincide costs one unit
of `2 ^ -128` and one whose public key encodes an address prefix costs `2 ^ -165`;
`WalkDefects` proves both, `prob_bad_walk` adds them, and `GoodWalk` is the walk that avoids
both. `pairedRun` and `pairedFused` play the game after a walk and keep the walk's value, and
`pairedRun_eq_map_pairedFused` relates the two presentations. -/

public section

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.Target

variable {γ : Type}

open Security CanonicalGraph WarmedGame

/-- A walk the three charges can be read against: its two seeds differ, and its public key is
no coincidence. -/
@[expose] def GoodWalk (walk : ((Digest × Digest × Digest) × Cells) × QueryCache HashSpec) : Prop :=
  walk.1.1.2.1 ≠ walk.1.1.2.2 ∧
    ¬ HashSeparation.Possible (walk.1.1.2.2, walk.1.2 (.structural WalkDefects.topNode))

/-- **Both of the walk's own coincidences, charged together.** -/
theorem prob_bad_walk :
    Pr{let walk ← graphWalk}[¬ GoodWalk walk] ≤
      1 / ((2 ^ 128 : Nat) : ℝ≥0∞) + 1 / ((2 ^ 165 : Nat) : ℝ≥0∞) := by
  classical
  refine le_trans (prEvent_mono graphWalk _ (fun walk => walk.1.1.2.1 = walk.1.1.2.2 ∨
    HashSeparation.Possible (walk.1.1.2.2, walk.1.2 (.structural WalkDefects.topNode)))
    fun walk hbad => ?_) ?_
  · by_cases hseeds : walk.1.1.2.1 = walk.1.1.2.2
    · exact Or.inl hseeds
    · exact Or.inr (by_contra fun hpossible => hbad ⟨hseeds, hpossible⟩)
  · exact le_trans (prEvent_or_le _ _ _)
      (add_le_add WalkDefects.prob_prf_eq_publicSeed_walk WalkDefects.prob_possible_walk)

/-! ## The walk and the game together

A charge whose secret is *in the walk* cannot be read at a fixed walk. Conditioning on the walk
fixes `SK.prf` and the cell table, and an adversary may have been chosen knowing them — for the
walk whose `SK.prf` is the constant it hardcodes, the event it is charged for happens with
probability one. A deferral draws its secret after the run, and that is
not available once the walk is a parameter.

So charges that defer a secret are stated *here*, on the walk and the game taken
together, where the walk's own randomness is still in the measure. The answer side is unaffected
and stays at a fixed walk: its charges are guesses at the tail's own fresh answers, which no
choice of adversary can bias in advance. -/

/-- The walk and the game that follows it, with the walk's value retained. -/
@[expose] noncomputable def pairedRun (adversary : Adversary) :
    ProbComp ((((Digest × Digest × Digest) × Cells) × QueryCache HashSpec) ×
      ((Outcome × Nat) × QueryCache HashSpec)) := do
  let walk ← graphWalk
  let result ← tail adversary walk
  pure (walk, result)

/-! ## The small defects

The walk's two coincidences cost `1 / 2 ^ 128` and `1 / 2 ^ 165`; `defectsAt` adds them to the
answer half's own term. -/

/-- The small defects, with the **answer half's own term a parameter**. The other two are the
walk's, and the walk pays them whatever the answer half's bound turns out to be. -/
@[expose] noncomputable def defectsAt (answerDefect : ℝ≥0∞) : ℝ≥0∞ :=
  answerDefect +
    ((1 : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) + (1 : ℝ≥0∞) / ((2 ^ 165 : Nat) : ℝ≥0∞))

attribute [local irreducible] WarmedGame.afterSeeds WarmedGame.graphWalk WarmedGame.tail
  WarmedGame.warmedRun Scheme.keygenInternal Scheme.verify Scheme.sign
  Security.signingOracle Security.countQueries

/-! ## At a tail that carries more than the game's result

Some of the answer side's events are not predicates of the game's result: late disclosure says
which of the recorder's two recordings an entry was filed on, and a result of `tail` carries no
recordings. So the paired run is restated here at an arbitrary tail that *refines* the game's:
any `fused` whose results forget to `tail`'s, with the forgetting map a parameter and the one
equation it has to satisfy a hypothesis.

Nothing about the presentation enters: the type is free, the map is free, and what makes the
restatement sound is `hforget` alone, an equality of computations. The walk's own two
coincidences are paid inside the refined paired run exactly as they are inside the plain one. -/

/-- The walk and a refining tail played from it. -/
@[expose] noncomputable def pairedFused {γ : Type}
    (fused : (((Digest × Digest × Digest) × Cells) × QueryCache HashSpec) → ProbComp γ) :
    ProbComp ((((Digest × Digest × Digest) × Cells) × QueryCache HashSpec) × γ) := do
  let walk ← graphWalk
  let result ← fused walk
  pure (walk, result)

/-- **The walk's own coincidences, read at the refined paired run.** -/
theorem prob_bad_walk_pairedFused {γ : Type}
    (fused : (((Digest × Digest × Digest) × Cells) × QueryCache HashSpec) → ProbComp γ) :
    Pr{let pair ← pairedFused fused}[¬ GoodWalk pair.1] ≤
      1 / ((2 ^ 128 : Nat) : ℝ≥0∞) + 1 / ((2 ^ 165 : Nat) : ℝ≥0∞) := by
  classical
  refine le_trans (WalkDefects.probEvent_bind_pair_split_le graphWalk fused
    (fun walk _ => ¬ GoodWalk walk) (fun walk => ¬ GoodWalk walk) 0
    fun walk _ hgood => ?_) ?_
  · rw [show (fun _ : γ => ¬ GoodWalk walk) = fun _ => False from by
      funext _; simp [not_not.mp hgood]]
    simp
  · rw [zero_add]
    exact prob_bad_walk

/-- **The refined paired run forgets to the plain one.** -/
theorem pairedRun_eq_map_pairedFused {γ : Type} (adversary : Adversary)
    (fused : (((Digest × Digest × Digest) × Cells) × QueryCache HashSpec) → ProbComp γ)
    (forget : γ → (Outcome × Nat) × QueryCache HashSpec)
    (hforget : ∀ walk, forget <$> fused walk = tail adversary walk) :
    pairedRun adversary = (fun pair => (pair.1, forget pair.2)) <$> pairedFused fused := by
  rw [pairedRun, pairedFused, map_bind]
  refine bind_congr fun walk => ?_
  rw [← hforget walk, map_eq_bind_pure_comp, map_eq_bind_pure_comp, bind_assoc, bind_assoc]
  exact bind_congr fun result => by rw [pure_bind]; rfl

end SlhDsaSecurity.Target
