/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Interval.Reductions.SourcePartition
import HashSig.GXMSS.Chain
import all HashSig.GXMSS.Merkle

/-!
# Interval source partition consumers and branch fixtures

Accepted examples exercise every partition branch, both kinds of active raw difference,
and both inactive families. Negative controls cover decoding failure and exact-pair replay.

Private imports supply the chain and Merkle computations used by these fixtures.
Ordinary endpoint applications use public imports.
-/

public section

open GXMSS GXMSS.IntervalMerkle GXMSS.Interval.Filler
open GXMSS.Interval GXMSS.Interval.Unforgeability
open SyncSignatureUnforgeability OracleSpec OracleComp

/-- Full-range inputs cannot occupy either of the two filler-opening branches. -/
theorem full_range_filler_partition {PP T X H M R : Type} {h w v : ℕ}
    [SampleableType H] [SampleableType R] [DecidableEq H] [DecidableEq M]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (K : ℕ) (pp : PP) (table : Fillers (Interval.full h) H)
    (out : ExperimentResult (GXMSS.PublicKey PP H) (Fin (2 ^ h)) M
      (GXMSS.Signature R H h v)) :
    (openingEvent P enc K (Interval.full h) .endpointVector pp table out,
      openingEvent P enc K (Interval.full h) .childPair pp table out) = (false, false) := by
  simp

private def middle : Interval 3 := ⟨3, 4, by decide⟩

private inductive TestInput where
  | digest : Bool → TestInput
  | pair : Bool × Bool → TestInput
  | vector : (Fin 1 → Bool) → TestInput

private inductive TestTweak where
  | chain : Fin 8 × Fin 1 × Fin 1 → TestTweak
  | tree : Fin 4 × Fin 8 → TestTweak
  deriving DecidableEq

private def testHash : HashInstance Unit TestTweak TestInput Bool 3 1 1 where
  thf := ⟨pure (), fun _ _ _ => false⟩
  digestInput := ⟨TestInput.digest, by intro a b hab; cases hab; rfl⟩
  pairInput := ⟨TestInput.pair, by intro a b hab; cases hab; rfl⟩
  vectorInput := ⟨TestInput.vector, by intro a b hab; cases hab; rfl⟩
  chainTweak := ⟨TestTweak.chain, by intro a b hab; cases hab; rfl⟩
  treeTweak := ⟨TestTweak.tree, by intro a b hab; cases hab; rfl⟩
  chain_ne_tree := by intro c t heq; cases heq

private def word : IncomparableEncoding.Codeword 1 2 := fun _ => 1

private def testEncoding : IncomparableEncoding Unit Bool Unit (Fin 8) 1 2 where
  code := {word}
  incomparable := by
    intro x hx y hy hne
    exact (hne ((Set.mem_singleton_iff.mp hx).trans (Set.mem_singleton_iff.mp hy).symm)).elim
  encode _ msg _ _ := if msg then some ⟨word, by simp⟩ else none

private def starts : Fin 8 → Fin 1 → Bool := fun _ _ => false

private def fillers (value : Bool) : Fillers middle Bool := fun _ => value

private def signature (vectorValue pathValue : Bool) : GXMSS.Signature Unit Bool 3 1 :=
  ⟨(), fun _ => vectorValue, fun _ => pathValue⟩

private instance signatureEquality : DecidableEq (GXMSS.Signature Unit Bool 3 1) := fun a b =>
  if h : (a.randomizer, a.ots, a.path) = (b.randomizer, b.ots, b.path) then
    isTrue (by cases a; cases b; simpa only [Prod.mk.injEq, GXMSS.Signature.mk.injEq] using h)
  else isFalse (by intro hab; subst b; exact h rfl)

private theorem test_endpoints : GXMSS.endpoints testHash () starts = fun _ _ => false := by
  funext e i
  change testHash.chain () e i 0 1 false = false
  exact (HashInstance.chain_succ testHash () e i 0 0 false (by decide)).trans rfl

private def sourceResult (fillerValue : Bool) (e : Fin 8) (msg : Bool)
    (sig : GXMSS.Signature Unit Bool 3 1)
    (history : History (Fin 8) Bool (GXMSS.Signature Unit Bool 3 1) := emptyHistory) :
    ExperimentResult (GXMSS.PublicKey Unit Bool) (Fin 8) Bool
      (GXMSS.Signature Unit Bool 3 1) :=
  ((GXMSS.Interval.keys testHash middle () starts (fillers fillerValue)).1,
    (e, msg, sig), history)

private noncomputable def branchBits (fillerValue : Bool) (e : Fin 8) (msg : Bool)
    (sig : GXMSS.Signature Unit Bool 3 1)
    (history : History (Fin 8) Bool (GXMSS.Signature Unit Bool 3 1) := emptyHistory) :
    Bool × Bool × Bool × Bool :=
  let (_, sk) := GXMSS.Interval.keys testHash middle () starts (fillers fillerValue)
  let out := sourceResult fillerValue e msg sig history
  (activeMatchingEvent testHash testEncoding 0 middle sk out,
    merkleObstructionEvent testHash testEncoding 0 middle sk out,
    openingEvent testHash testEncoding 0 middle .endpointVector () (fillers fillerValue) out,
    openingEvent testHash testEncoding 0 middle .childPair () (fillers fillerValue) out)

/-- An active accepted fresh signature with identical recovered vector and path selects A. -/
private theorem active_matching :
    branchBits false 3 true (signature false false) = (true, false, false, false) := by
  simp only [branchBits, activeMatchingEvent, merkleObstructionEvent, sourceResult,
    GXMSS.Interval.keys, GXMSS.keys, test_endpoints]
  simp only [Nat.reducePow, testEncoding, Fin.isValue, signature,
    IncomparableEncoding.value, ↓reduceIte, Option.map_some, word,
    Fin.coe_ofNat_eq_mod, Nat.mod_succ, pow_one, Nat.add_one_sub_one, tsub_self,
    HashInstance.chain_zero, Prod.mk.injEq, true_and, Bool.decide_and, ne_eq, decide_not,
    Bool.and_eq_true, decide_eq_true_eq, Bool.and_eq_false_imp]
  decide

/-- Changing only the active recovered vector selects M while verification remains true. -/
private theorem active_vector_difference :
    branchBits false 3 true (signature true false) = (false, true, false, false) := by
  simp only [branchBits, activeMatchingEvent, merkleObstructionEvent, sourceResult,
    GXMSS.Interval.keys, GXMSS.keys, test_endpoints]
  simp only [Nat.reducePow, testEncoding, Fin.isValue, signature,
    IncomparableEncoding.value, ↓reduceIte, Option.map_some, word,
    Fin.coe_ofNat_eq_mod, Nat.mod_succ, pow_one, Nat.add_one_sub_one, tsub_self,
    HashInstance.chain_zero, Prod.mk.injEq, Bool.decide_and, ne_eq, not_and,
    decide_implies, decide_not, dite_eq_ite, Bool.ite_true_right, Bool.and_eq_false_imp,
    decide_eq_true_eq, decide_eq_false_iff_not, Bool.and_eq_true]
  decide

/-- Changing only the active submitted path selects M while verification remains true. -/
private theorem active_path_difference :
    branchBits false 3 true (signature false true) = (false, true, false, false) := by
  simp only [branchBits, activeMatchingEvent, merkleObstructionEvent, sourceResult,
    GXMSS.Interval.keys, GXMSS.keys, test_endpoints]
  simp only [Nat.reducePow, testEncoding, Fin.isValue, signature,
    IncomparableEncoding.value, ↓reduceIte, Option.map_some, word,
    Fin.coe_ofNat_eq_mod, Nat.mod_succ, pow_one, Nat.add_one_sub_one, tsub_self,
    HashInstance.chain_zero, Prod.mk.injEq, true_and, Bool.decide_and, ne_eq, decide_not,
    Bool.and_eq_false_imp, decide_eq_true_eq, decide_eq_false_iff_not, Bool.and_eq_true]
  decide

/-- Height-zero frontier equality selects the actual vector-opening event. -/
private theorem inactive_vector :
    branchBits false 5 true (signature false false) = (false, false, true, false) := by decide

/-- A positive frontier height selects the actual ordered-child-pair opening event. -/
private theorem inactive_pair :
    branchBits false 0 true (signature false false) = (false, false, false, true) := by decide

/-- An accepted inactive opening with a different computed frontier selects M. -/
private theorem inactive_frontier_difference :
    branchBits true 0 true (signature false false) = (false, true, false, false) := by decide

/-- Failed decoding suppresses all four events, including both inactive opening families. -/
private theorem decoding_failure (e : Fin 8) :
    branchBits false e false (signature false false) = (false, false, false, false) := by
  simp [branchBits, activeMatchingEvent, merkleObstructionEvent, openingEvent,
    extractFillerOpening, sourceResult, strongValid, GXMSS.Interval.scheme,
    GXMSS.Interval.verify, GXMSS.verify, testEncoding, IncomparableEncoding.value]

/-- Replaying the exact returned message/signature pair suppresses all four events. -/
private theorem exact_pair_replay (e : Fin 8) :
    branchBits false e true (signature false false)
      (Function.update emptyHistory e (some (true, some (signature false false)))) =
        (false, false, false, false) := by
  simp [branchBits, activeMatchingEvent, merkleObstructionEvent, openingEvent,
    extractFillerOpening, sourceResult, strongValid, strongFresh, Function.update]

/-- A prior different signature at the same message and epoch remains strongly fresh. -/
private theorem different_pair_fresh :
    branchBits false 3 true (signature false false)
      (Function.update emptyHistory 3 (some (true, some (signature true false)))) =
        (true, false, false, false) := by
  simp only [branchBits, activeMatchingEvent, merkleObstructionEvent, sourceResult,
    GXMSS.Interval.keys, GXMSS.keys, test_endpoints]
  simp only [Nat.reducePow, testEncoding, Fin.isValue, signature,
    IncomparableEncoding.value, ↓reduceIte, Option.map_some, word,
    Fin.coe_ofNat_eq_mod, Nat.mod_succ, pow_one, Nat.add_one_sub_one, tsub_self,
    HashInstance.chain_zero, Prod.mk.injEq, true_and, Bool.decide_and, ne_eq, decide_not,
    Bool.and_eq_true, decide_eq_true_eq, Bool.and_eq_false_imp]
  decide

private theorem pointwise_partition_fixture (fillerValue : Bool) (e : Fin 8) (msg : Bool)
    (sig : GXMSS.Signature Unit Bool 3 1) :
    let (_, sk) := GXMSS.Interval.keys testHash middle () starts (fillers fillerValue)
    let out := sourceResult fillerValue e msg sig
    let a := activeMatchingEvent testHash testEncoding 0 middle sk out
    let m := merkleObstructionEvent testHash testEncoding 0 middle sk out
    let fv := openingEvent testHash testEncoding 0 middle .endpointVector ()
      (fillers fillerValue) out
    let fp := openingEvent testHash testEncoding 0 middle .childPair ()
      (fillers fillerValue) out
    strongValid (GXMSS.Interval.scheme testHash testEncoding 0 middle) out =
        (a || m || fv || fp) ∧
      (a && m) = false ∧ (a && fv) = false ∧ (a && fp) = false ∧
      (m && fv) = false ∧ (m && fp) = false ∧ (fv && fp) = false :=
  sourceStrongObservation_partition testHash testEncoding 0 middle _ _
    (GXMSS.Interval.consistent_keys testHash middle () starts (fillers fillerValue))

private theorem native_mass_partition_fixture
    (A : Adversary unifSpec (GXMSS.PublicKey Unit Bool) (Fin 8) Bool
    (GXMSS.Signature Unit Bool 3 1)) :
    strongAdvantage (GXMSS.Interval.scheme testHash testEncoding 0 middle)
        ProbCompRuntime.probComp A =
      ProbCompRuntime.probComp.evalDist
        (activeMatchingExperiment testHash testEncoding 0 middle A) {true} +
        ProbCompRuntime.probComp.evalDist
          (merkleObstructionExperiment testHash testEncoding 0 middle A) {true} +
        ProbCompRuntime.probComp.evalDist
          (sourceOpening testHash testEncoding 0 middle A .endpointVector) {true} +
        ProbCompRuntime.probComp.evalDist
          (sourceOpening testHash testEncoding 0 middle A .childPair) {true} :=
  strongAdvantage_eq_source_partition testHash testEncoding 0 middle A

private theorem primitive_bound_fixture
    (A : Adversary unifSpec (GXMSS.PublicKey Unit Bool) (Fin 8) Bool
    (GXMSS.Signature Unit Bool 3 1)) :
    strongAdvantage (GXMSS.Interval.scheme testHash testEncoding 0 middle)
        ProbCompRuntime.probComp A ≤
      ProbCompRuntime.probComp.evalDist
        (activeMatchingExperiment testHash testEncoding 0 middle A) {true} +
        ProbCompRuntime.probComp.evalDist
          (merkleObstructionExperiment testHash testEncoding 0 middle A) {true} +
        TweakableHash.SM_DT_UD_Advantage
          (udAdversary testHash testEncoding 0 middle A .endpointVector) +
        TweakableHash.SM_DT_PRE_Advantage
          (preAdversary testHash testEncoding 0 middle A .endpointVector) +
        TweakableHash.SM_DT_UD_Advantage
          (udAdversary testHash testEncoding 0 middle A .childPair) +
        TweakableHash.SM_DT_PRE_Advantage
          (preAdversary testHash testEncoding 0 middle A .childPair) :=
  strongAdvantage_le_merkle_active_and_filler_advantages testHash testEncoding 0 middle A
