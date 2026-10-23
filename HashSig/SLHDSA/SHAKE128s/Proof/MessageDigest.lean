/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.Experiment
public import VCVio.OracleComp.Constructions.SampleableType

/-! The full parsed digest has the independent uniform distribution used in FORS counting. -/

@[expose] public section

open OracleComp OracleSpec

namespace SlhDsaSecurity.MessageDigest

/-- Retaining the discarded bits makes the standard parser a bijection. -/
def split (output : HashOutput) : View × (BitVec 2 × BitVec 7) :=
  (parse output, output.extractLsb' 70 2, output.extractLsb' 9 7)

theorem split_injective : Function.Injective split := by
  intro left right heq
  have hinstance : treeIndex left ++ leafIndex left = treeIndex right ++ leafIndex right :=
    BitVec.toFin_injective (congrArg (fun x => x.1.1) heq)
  have hleaves : forsIndices left = forsIndices right := congrArg (fun x => x.1.2) heq
  have hunusedTree := congrArg (fun x => x.2.1) heq
  have hunusedLeaf := congrArg (fun x => x.2.2) heq
  apply BitVec.eq_of_getLsbD_eq
  intro bit hbit
  change bit < 240 at hbit
  by_cases hleaf : bit < 9
  · have h := congrArg (fun value => value.getLsbD bit) hinstance
    rw [BitVec.getLsbD_append, BitVec.getLsbD_append] at h
    simpa only [subtreeHeight, leafIndex, BitVec.getLsbD_extractLsb', hleaf,
      decide_true, Bool.true_and, Nat.zero_add, ite_true] using h
  by_cases hleafPad : bit < 16
  · have h := congrArg (fun value => value.getLsbD (bit - 9)) hunusedLeaf
    have hlocal : bit - 9 < 7 := by omega
    have hposition : 9 + (bit - 9) = bit := by omega
    simpa [split, BitVec.getLsbD_extractLsb', hlocal, hposition] using h
  by_cases htree : bit < 70
  · have h := congrArg (fun value => value.getLsbD (bit - 7)) hinstance
    rw [BitVec.getLsbD_append, BitVec.getLsbD_append] at h
    have hnotlow : ¬ bit - 7 < 9 := by omega
    have hlocal : bit - 7 - 9 < 54 := by omega
    have hposition : 16 + (bit - 7 - 9) = bit := by omega
    simpa only [subtreeHeight, if_neg hnotlow, treeIndex,
      totalHeight, Nat.reduceSub, BitVec.getLsbD_extractLsb', hlocal, decide_true,
      Bool.true_and, hposition] using h
  by_cases htreePad : bit < 72
  · have h := congrArg (fun value => value.getLsbD (bit - 70)) hunusedTree
    have hlocal : bit - 70 < 2 := by omega
    have hposition : 70 + (bit - 70) = bit := by omega
    simpa [split, BitVec.getLsbD_extractLsb', hlocal, hposition] using h
  · let digit : ForsTree := ⟨13 - (bit - 72) / 12, by change _ < 14; omega⟩
    have hdigit : left.extractLsb' (72 + forsHeight * (forsTrees - 1 - digit.val)) forsHeight =
        right.extractLsb' (72 + forsHeight * (forsTrees - 1 - digit.val)) forsHeight :=
      BitVec.toFin_injective (congrFun hleaves digit)
    have h := congrArg (fun value => value.getLsbD ((bit - 72) % 12)) hdigit
    have hlocal : (bit - 72) % 12 < 12 := Nat.mod_lt _ (by decide)
    have hposition : 72 + 12 * (14 - 1 - digit.val) + (bit - 72) % 12 = bit := by
      dsimp [digit]
      omega
    simpa only [forsHeight, forsTrees, BitVec.getLsbD_extractLsb', hlocal, decide_true,
      Bool.true_and, hposition] using h

theorem split_bijective : Function.Bijective split := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  refine ⟨split_injective, ?_⟩
  norm_num [HashOutput, messageDigestBytes, View, Instance, ForsTree, ForsLeaf,
    Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, card_bitVec,
    totalHeight, forsHeight, forsTrees]

end SlhDsaSecurity.MessageDigest
