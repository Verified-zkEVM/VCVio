/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Interval.Auxiliary.MerkleWitnesses.Collision

/-!
# Raw inactive frontier openings

An accepted inactive opening either yields an addressed collision above the frontier or an
actual vector/pair preimage of its stored digest, with no hash-domain enumeration.
-/

public section

namespace GXMSS.Interval.MerkleWitnesses

open GXMSS GXMSS.IntervalMerkle BinaryTree AddressedMerkleTree PerfectMerkleTree

variable {PP T X H : Type} {h w v : ℕ}

/-- Ordered raw pair supplied to the original pair hash at a positive frontier height.
The nonempty path prefix is guaranteed by the positive height. -/
@[expose] def openingFrontierPair (P : HashInstance PP T X H h w v)
    (I : GXMSS.IntervalMerkle.Interval h) (pp : PP) (e : Fin (2 ^ h))
    (he : ¬ GXMSS.IntervalMerkle.Epoch.IsActive I e)
    (hz : 0 < GXMSS.IntervalMerkle.frontierLevel I e)
    (ys : Fin v → H) (auth : Fin h → H) : H × H := by
  let z := GXMSS.IntervalMerkle.frontierLevel I e
  let lower := (List.ofFn auth).take z
  have hzle : z ≤ h := (GXMSS.IntervalMerkle.frontierLevel_isInactiveFrontier I e he).height_le
  have hlen : lower.length = z := by simp [lower, hzle]
  have hn : lower ≠ [] := by
    intro hnil
    have : z = 0 := by simpa [hnil] using hlen.symm
    omega
  let first := PerfectMerkleTree.climb (GXMSS.IntervalMerkle.ordinaryNode P pp) e.val
    (P.leafHash pp e ys) lower.dropLast
  let sibling := lower.getLast hn
  exact if e.val / 2 ^ (z - 1) % 2 = 0 then (first, sibling) else (sibling, first)

/-- Positive frontier digests are original addressed pair-hash outputs of the exact
ordered opening input computed above. -/
theorem openingFrontierDigest_eq_pair (P : HashInstance PP T X H h w v)
    (I : GXMSS.IntervalMerkle.Interval h) (pp : PP) (e : Fin (2 ^ h))
    (he : ¬ GXMSS.IntervalMerkle.Epoch.IsActive I e)
    (hz : 0 < GXMSS.IntervalMerkle.frontierLevel I e)
    (ys : Fin v → H) (auth : Fin h → H) :
    let z := GXMSS.IntervalMerkle.frontierLevel I e
    openingFrontierDigest P I pp e ys auth =
      P.nodeHash pp
        ⟨z, Nat.lt_succ_of_le (GXMSS.IntervalMerkle.frontierLevel_isInactiveFrontier I e
            he).height_le⟩
        ⟨e.val / 2 ^ z,
          (PerfectMerkleTree.ancestor_legal e z
            (GXMSS.IntervalMerkle.frontierLevel_isInactiveFrontier I e he).height_le).2⟩
        (openingFrontierPair P I pp e he hz ys auth).1
        (openingFrontierPair P I pp e he hz ys auth).2 := by
  dsimp only
  let z := GXMSS.IntervalMerkle.frontierLevel I e
  let lower := (List.ofFn auth).take z
  have hzle : z ≤ h := (GXMSS.IntervalMerkle.frontierLevel_isInactiveFrontier I e he).height_le
  have hlen : lower.length = z := by simp [lower, hzle]
  have hn : lower ≠ [] := by
    intro hnil
    have : z = 0 := by simpa [hnil] using hlen.symm
    omega
  have hlast : lower.dropLast ++ [lower.getLast hn] = lower :=
    List.dropLast_append_getLast hn
  let lowerPath := lower.dropLast
  have hprefix : lowerPath.length = z - 1 := by
    dsimp only [lowerPath]
    have hlen' := congrArg List.length hlast
    simp only [List.length_append, List.length_singleton] at hlen'
    omega
  have hstep := congrArg Id.run (PerfectMerkleTree.climbM_concat (m := Id)
    (GXMSS.IntervalMerkle.ordinaryNode P pp) e.val (P.leafHash pp e ys)
    lower.dropLast (lower.getLast hn))
  simp only [PerfectMerkleTree.idRun_climbM, Id.run_bind] at hstep
  simp only [Id.run] at hstep
  have hraw : openingFrontierDigest P I pp e ys auth =
      if e.val / 2 ^ (z - 1) % 2 = 0 then
        GXMSS.IntervalMerkle.ordinaryNode P pp z (e.val / 2 ^ z)
          (climb (GXMSS.IntervalMerkle.ordinaryNode P pp) e.val (P.leafHash pp e ys)
            lower.dropLast) (lower.getLast hn)
      else GXMSS.IntervalMerkle.ordinaryNode P pp z (e.val / 2 ^ z)
          (lower.getLast hn)
          (climb (GXMSS.IntervalMerkle.ordinaryNode P pp) e.val (P.leafHash pp e ys)
            lower.dropLast) := by
    unfold openingFrontierDigest
    change climb (GXMSS.IntervalMerkle.ordinaryNode P pp) e.val (P.leafHash pp e ys) lower = _
    calc
      _ = climb (GXMSS.IntervalMerkle.ordinaryNode P pp) e.val (P.leafHash pp e ys)
            (lower.dropLast ++ [lower.getLast hn]) := by rw [hlast]
      _ = _ := by
        rw [hstep, hprefix]
        simp only [Nat.sub_add_cancel (by omega : 1 ≤ z)]
  have hnode (l r : H) : GXMSS.IntervalMerkle.ordinaryNode P pp z (e.val / 2 ^ z) l r =
      P.nodeHash pp ⟨z, by omega⟩
        ⟨e.val / 2 ^ z, (PerfectMerkleTree.ancestor_legal e z hzle).2⟩ l r := by
    unfold GXMSS.IntervalMerkle.ordinaryNode
    rw [dite_eq_left (by omega : z < h + 1)]
    rw [dite_eq_left (PerfectMerkleTree.ancestor_legal e z hzle).2]
  have hpair : openingFrontierPair P I pp e he hz ys auth =
      if e.val / 2 ^ (z - 1) % 2 = 0 then
        (climb (GXMSS.IntervalMerkle.ordinaryNode P pp) e.val (P.leafHash pp e ys)
          lower.dropLast, lower.getLast hn)
      else (lower.getLast hn,
        climb (GXMSS.IntervalMerkle.ordinaryNode P pp) e.val (P.leafHash pp e ys)
          lower.dropLast) := by
    rfl
  rw [hpair, hraw]
  by_cases hbit : e.val / 2 ^ (z - 1) % 2 = 0
  · simp only [hbit, ite_true, hnode]
    rfl
  · simp only [hbit, ite_false, hnode]
    rfl

/-- Equality with the stored filler gives an explicit original-domain preimage: a raw
endpoint vector at height zero or an ordered pair at positive height. -/
theorem filler_preimage_of_equal (P : HashInstance PP T X H h w v)
    (I : GXMSS.IntervalMerkle.Interval h) (pp : PP) (e : Fin (2 ^ h))
    (he : ¬ GXMSS.IntervalMerkle.Epoch.IsActive I e) (ys : Fin v → H) (auth : Fin h → H)
    (fillers : GXMSS.IntervalMerkle.Fillers I H)
    (heq : openingFrontierDigest P I pp e ys auth =
      GXMSS.IntervalMerkle.frontierValue I fillers
        (GXMSS.IntervalMerkle.frontierLevel I e)
        (e.val / 2 ^ GXMSS.IntervalMerkle.frontierLevel I e)
        (GXMSS.IntervalMerkle.frontierLevel_isInactiveFrontier I e he)) :
    let z := GXMSS.IntervalMerkle.frontierLevel I e
    (z = 0 ∧ P.leafHash pp e ys =
      GXMSS.IntervalMerkle.frontierValue I fillers z (e.val / 2 ^ z)
        (GXMSS.IntervalMerkle.frontierLevel_isInactiveFrontier I e he)) ∨
    (∃ hz : 0 < z,
      P.nodeHash pp
        ⟨z, Nat.lt_succ_of_le (GXMSS.IntervalMerkle.frontierLevel_isInactiveFrontier I e
            he).height_le⟩
        ⟨e.val / 2 ^ z,
          (PerfectMerkleTree.ancestor_legal e z
            (GXMSS.IntervalMerkle.frontierLevel_isInactiveFrontier I e he).height_le).2⟩
        (openingFrontierPair P I pp e he hz ys auth).1
        (openingFrontierPair P I pp e he hz ys auth).2 =
      GXMSS.IntervalMerkle.frontierValue I fillers z (e.val / 2 ^ z)
        (GXMSS.IntervalMerkle.frontierLevel_isInactiveFrontier I e he)) := by
  dsimp only
  by_cases hz : GXMSS.IntervalMerkle.frontierLevel I e = 0
  · left
    refine ⟨hz, ?_⟩
    have hzero : climb (GXMSS.IntervalMerkle.ordinaryNode P pp) e.val
        (P.leafHash pp e ys) [] = P.leafHash pp e ys := rfl
    simpa only [openingFrontierDigest, hz, List.take_zero, hzero, pow_zero,
      Nat.div_one] using heq
  · right
    have hzpos : 0 < GXMSS.IntervalMerkle.frontierLevel I e := by omega
    have hpair := openingFrontierDigest_eq_pair P I pp e he hzpos ys auth
    exact ⟨hzpos, Eq.trans hpair.symm heq⟩

/-- A verifier-accepted signature gives a successful encoded word and the exact
unrestricted recovered-root equation. The verifier has no active-range guard. -/
theorem accepted_opening [DecidableEq H]
    {M R : Type} (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (I : GXMSS.IntervalMerkle.Interval h) (pp : PP)
    (xs : Fin (2 ^ h) → Fin v → H) (fillers : GXMSS.IntervalMerkle.Fillers I H)
    (e : Fin (2 ^ h)) (msg : M) (sig : GXMSS.Signature R H h v)
    (hv : GXMSS.Interval.verify P enc
      ⟨GXMSS.IntervalMerkle.root P I pp xs fillers, pp⟩ e msg sig = true) :
    ∃ word : IncomparableEncoding.Codeword v (2 ^ w),
      enc.value pp msg sig.randomizer e = some word ∧
      P.recoverRoot pp e
        (fun i => P.chain pp e i (word i) (2 ^ w - 1 - (word i).val) (sig.ots i))
        sig.path = GXMSS.IntervalMerkle.root P I pp xs fillers := by
  simp only [GXMSS.Interval.verify, GXMSS.verify] at hv
  cases hw : enc.value pp msg sig.randomizer e with
  | none => simp [hw] at hv
  | some word =>
    refine ⟨word, by simp, ?_⟩
    simpa only [hw, decide_eq_true_eq] using hv

/-- The explicit original-domain preimage alternatives at the unique frontier. -/
@[expose] def FrontierPreimage (P : HashInstance PP T X H h w v)
    (I : GXMSS.IntervalMerkle.Interval h) (pp : PP) (e : Fin (2 ^ h))
    (he : ¬ GXMSS.IntervalMerkle.Epoch.IsActive I e) (ys : Fin v → H)
    (auth : Fin h → H) (fillers : GXMSS.IntervalMerkle.Fillers I H) : Prop :=
  let z := GXMSS.IntervalMerkle.frontierLevel I e
  (z = 0 ∧ P.leafHash pp e ys =
    GXMSS.IntervalMerkle.frontierValue I fillers z (e.val / 2 ^ z)
      (GXMSS.IntervalMerkle.frontierLevel_isInactiveFrontier I e he)) ∨
  (∃ hz : 0 < z,
    P.nodeHash pp
      ⟨z, Nat.lt_succ_of_le (GXMSS.IntervalMerkle.frontierLevel_isInactiveFrontier I e
          he).height_le⟩
      ⟨e.val / 2 ^ z,
        (PerfectMerkleTree.ancestor_legal e z
          (GXMSS.IntervalMerkle.frontierLevel_isInactiveFrontier I e he).height_le).2⟩
      (openingFrontierPair P I pp e he hz ys auth).1
      (openingFrontierPair P I pp e he hz ys auth).2 =
        GXMSS.IntervalMerkle.frontierValue I fillers z (e.val / 2 ^ z)
          (GXMSS.IntervalMerkle.frontierLevel_isInactiveFrontier I e he))

/-- A returned raw payload itself hashes to the filler at its unique frontier address. -/
@[expose] def RawFrontierPreimage (P : HashInstance PP T X H h w v)
    (I : GXMSS.IntervalMerkle.Interval h) (pp : PP) (e : Fin (2 ^ h))
    (he : ¬ GXMSS.IntervalMerkle.Epoch.IsActive I e) (fillers : GXMSS.IntervalMerkle.Fillers I H)
    (raw : Sum (Fin v → H) (H × H)) : Prop :=
  let z := GXMSS.IntervalMerkle.frontierLevel I e
  match raw with
  | .inl vector =>
    z = 0 ∧ P.leafHash pp e vector =
      GXMSS.IntervalMerkle.frontierValue I fillers z (e.val / 2 ^ z)
        (GXMSS.IntervalMerkle.frontierLevel_isInactiveFrontier I e he)
  | .inr pair =>
    ∃ _hz : 0 < z,
      P.nodeHash pp
        ⟨z, Nat.lt_succ_of_le (GXMSS.IntervalMerkle.frontierLevel_isInactiveFrontier I e
            he).height_le⟩
        ⟨e.val / 2 ^ z,
          (PerfectMerkleTree.ancestor_legal e z
            (GXMSS.IntervalMerkle.frontierLevel_isInactiveFrontier I e he).height_le).2⟩
        pair.1 pair.2 =
          GXMSS.IntervalMerkle.frontierValue I fillers z (e.val / 2 ^ z)
            (GXMSS.IntervalMerkle.frontierLevel_isInactiveFrontier I e he)

/-- Compute the raw vector or ordered pair when the opening frontier digest equals its
sampled filler; otherwise run the finite oriented collision search. On arbitrary openings
the latter may return `none`. -/
@[expose] def extractInactiveOpening [DecidableEq H]
    (P : HashInstance PP T X H h w v) (I : GXMSS.IntervalMerkle.Interval h)
    (pp : PP) (xs : Fin (2 ^ h) → Fin v → H)
    (fillers : GXMSS.IntervalMerkle.Fillers I H) (e : Fin (2 ^ h))
    (he : ¬ GXMSS.IntervalMerkle.Epoch.IsActive I e) (ys : Fin v → H) (auth : Fin h → H) :
    Sum (Sum (Fin v → H) (H × H)) (Option (ℕ × (H × H) × (H × H))) :=
  if openingFrontierDigest P I pp e ys auth =
      GXMSS.IntervalMerkle.frontierValue I fillers
        (GXMSS.IntervalMerkle.frontierLevel I e)
        (e.val / 2 ^ GXMSS.IntervalMerkle.frontierLevel I e)
        (GXMSS.IntervalMerkle.frontierLevel_isInactiveFrontier I e he) then
    if hz : GXMSS.IntervalMerkle.frontierLevel I e = 0 then
      .inl (.inl ys)
    else
      .inl (.inr (openingFrontierPair P I pp e he (Nat.pos_of_ne_zero hz) ys auth))
  else
    .inr (findAboveFrontier P I pp xs fillers e ys auth)

/-- The unequal-frontier branch runs exactly the finite quotient collision finder. -/
theorem extractInactiveOpening_of_unequal [DecidableEq H]
    (P : HashInstance PP T X H h w v) (I : GXMSS.IntervalMerkle.Interval h)
    (pp : PP) (xs : Fin (2 ^ h) → Fin v → H)
    (fillers : GXMSS.IntervalMerkle.Fillers I H) (e : Fin (2 ^ h))
    (he : ¬ GXMSS.IntervalMerkle.Epoch.IsActive I e) (ys : Fin v → H) (auth : Fin h → H)
    (hne : openingFrontierDigest P I pp e ys auth ≠
      GXMSS.IntervalMerkle.frontierValue I fillers
        (GXMSS.IntervalMerkle.frontierLevel I e)
        (e.val / 2 ^ GXMSS.IntervalMerkle.frontierLevel I e)
        (GXMSS.IntervalMerkle.frontierLevel_isInactiveFrontier I e he)) :
    extractInactiveOpening P I pp xs fillers e he ys auth =
      .inr (findAboveFrontier P I pp xs fillers e ys auth) := by
  simp [extractInactiveOpening, hne]

/-- The equal-frontier branch computes the raw vector or pair and proves its
original-domain filler preimage equation. -/
theorem extractInactiveOpening_of_equal [DecidableEq H]
    (P : HashInstance PP T X H h w v) (I : GXMSS.IntervalMerkle.Interval h)
    (pp : PP) (xs : Fin (2 ^ h) → Fin v → H)
    (fillers : GXMSS.IntervalMerkle.Fillers I H) (e : Fin (2 ^ h))
    (he : ¬ GXMSS.IntervalMerkle.Epoch.IsActive I e) (ys : Fin v → H) (auth : Fin h → H)
    (heq : openingFrontierDigest P I pp e ys auth =
      GXMSS.IntervalMerkle.frontierValue I fillers
        (GXMSS.IntervalMerkle.frontierLevel I e)
        (e.val / 2 ^ GXMSS.IntervalMerkle.frontierLevel I e)
        (GXMSS.IntervalMerkle.frontierLevel_isInactiveFrontier I e he)) :
    ∃ raw : Sum (Fin v → H) (H × H),
      extractInactiveOpening P I pp xs fillers e he ys auth = .inl raw ∧
        RawFrontierPreimage P I pp e he fillers raw ∧
        FrontierPreimage P I pp e he ys auth fillers := by
  by_cases hz : GXMSS.IntervalMerkle.frontierLevel I e = 0
  · have hpre := filler_preimage_of_equal P I pp e he ys auth fillers heq
    have hleaf : P.leafHash pp e ys =
        GXMSS.IntervalMerkle.frontierValue I fillers
          (GXMSS.IntervalMerkle.frontierLevel I e)
          (e.val / 2 ^ GXMSS.IntervalMerkle.frontierLevel I e)
          (GXMSS.IntervalMerkle.frontierLevel_isInactiveFrontier I e he) := by
      rcases hpre with hvec | hpair
      · exact hvec.2
      · obtain ⟨hpos, _⟩ := hpair
        omega
    refine ⟨.inl ys, ?_, ?_, hpre⟩
    · simp [extractInactiveOpening, heq, hz]
    · exact ⟨hz, hleaf⟩
  · have hzpos : 0 < GXMSS.IntervalMerkle.frontierLevel I e := Nat.pos_of_ne_zero hz
    have hpre := filler_preimage_of_equal P I pp e he ys auth fillers heq
    have hpair : P.nodeHash pp
        ⟨GXMSS.IntervalMerkle.frontierLevel I e,
          by have := (GXMSS.IntervalMerkle.frontierLevel_isInactiveFrontier I e he).height_le;
              omega⟩
        ⟨e.val / 2 ^ GXMSS.IntervalMerkle.frontierLevel I e,
          (PerfectMerkleTree.ancestor_legal e (GXMSS.IntervalMerkle.frontierLevel I e)
            (GXMSS.IntervalMerkle.frontierLevel_isInactiveFrontier I e he).height_le).2⟩
        (openingFrontierPair P I pp e he hzpos ys auth).1
        (openingFrontierPair P I pp e he hzpos ys auth).2 =
          GXMSS.IntervalMerkle.frontierValue I fillers
            (GXMSS.IntervalMerkle.frontierLevel I e)
            (e.val / 2 ^ GXMSS.IntervalMerkle.frontierLevel I e)
            (GXMSS.IntervalMerkle.frontierLevel_isInactiveFrontier I e he) := by
      rcases hpre with hvec | ⟨hz', hp⟩
      · omega
      · exact hp
    refine ⟨.inr (openingFrontierPair P I pp e he hzpos ys auth), ?_, ?_, hpre⟩
    · simp [extractInactiveOpening, heq, hz]
    · exact ⟨hzpos, hpair⟩

/-- An inactive opening reaching the honest mixed root deterministically yields either
the frontier filler's raw preimage or an oriented original-THF collision above it. -/
theorem inactive_opening_decomposition [DecidableEq H]
    (P : HashInstance PP T X H h w v) (I : GXMSS.IntervalMerkle.Interval h)
    (pp : PP) (xs : Fin (2 ^ h) → Fin v → H)
    (fillers : GXMSS.IntervalMerkle.Fillers I H) (e : Fin (2 ^ h))
    (he : ¬ GXMSS.IntervalMerkle.Epoch.IsActive I e) (ys : Fin v → H) (auth : Fin h → H)
    (hroot : P.recoverRoot pp e ys auth = GXMSS.IntervalMerkle.root P I pp xs fillers) :
    FrontierPreimage P I pp e he ys auth fillers ∨
      ∃ q first second, ∃ address : Fin (h + 1) × Fin (2 ^ h),
        let (subtreeHeight, subtreeIndex) := address
        findAboveFrontier P I pp xs fillers e ys auth = some (q, first, second) ∧
        subtreeHeight.val = GXMSS.IntervalMerkle.frontierLevel I e + q ∧
        subtreeIndex.val = e.val / 2 ^ (GXMSS.IntervalMerkle.frontierLevel I e + q) ∧
        GXMSS.IntervalMerkle.frontierLevel I e < subtreeHeight.val ∧
        first = PerfectMerkleTree.honestChildren
          (fun i => GXMSS.IntervalMerkle.subtreeRoot P I pp xs fillers
            (GXMSS.IntervalMerkle.frontierLevel I e) i)
          (fun j i => GXMSS.IntervalMerkle.node P I pp fillers
            (GXMSS.IntervalMerkle.frontierLevel I e + j) i)
          q ((e.val / 2 ^ GXMSS.IntervalMerkle.frontierLevel I e) / 2 ^ q) ∧
        (GXMSS.Security.HashCollision.mk (P.treeTweak address)
          (P.pairInput first) (P.pairInput second)).Sound P.thf pp ∧
        (P.treeTweak address, P.pairInput first) ∈
          honestTargetQueries P I pp xs fillers := by
  by_cases heq : openingFrontierDigest P I pp e ys auth =
      GXMSS.IntervalMerkle.frontierValue I fillers
        (GXMSS.IntervalMerkle.frontierLevel I e)
        (e.val / 2 ^ GXMSS.IntervalMerkle.frontierLevel I e)
        (GXMSS.IntervalMerkle.frontierLevel_isInactiveFrontier I e he)
  · exact Or.inl (filler_preimage_of_equal P I pp e he ys auth fillers heq)
  · obtain ⟨q, second, hfind⟩ := findAboveFrontier_oriented P I pp xs fillers e
      he ys auth hroot (Ne.symm heq)
    let first := PerfectMerkleTree.honestChildren
      (fun i => GXMSS.IntervalMerkle.subtreeRoot P I pp xs fillers
        (GXMSS.IntervalMerkle.frontierLevel I e) i)
      (fun j i => GXMSS.IntervalMerkle.node P I pp fillers
        (GXMSS.IntervalMerkle.frontierLevel I e + j) i)
      q ((e.val / 2 ^ GXMSS.IntervalMerkle.frontierLevel I e) / 2 ^ q)
    obtain ⟨address, hlevel, hindex, habove, hfirst, hne, hhash, htarget⟩ :=
      findAboveFrontier_sound P I pp xs fillers e he ys auth q first second
        hfind hroot (Ne.symm heq)
    have hcollision : (GXMSS.Security.HashCollision.mk (P.treeTweak address)
        (P.pairInput first) (P.pairInput second)).Sound P.thf pp := by
      exact GXMSS.Security.collision_embedding P.thf pp (P.treeTweak address)
        P.pairInput hne hhash
    exact Or.inr ⟨q, first, second, address, hfind, hlevel, hindex, habove,
      hfirst, hcollision, htarget⟩

/-- The verifier's accepted inactive signature reaches the same concrete decomposition.
Successful encoding and its recovered endpoint vector are retained explicitly. -/
theorem accepted_inactive_decomposition [DecidableEq H]
    {M R : Type} (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (I : GXMSS.IntervalMerkle.Interval h) (pp : PP)
    (xs : Fin (2 ^ h) → Fin v → H) (fillers : GXMSS.IntervalMerkle.Fillers I H)
    (e : Fin (2 ^ h)) (he : ¬ GXMSS.IntervalMerkle.Epoch.IsActive I e)
    (msg : M) (sig : GXMSS.Signature R H h v)
    (hv : GXMSS.Interval.verify P enc
      ⟨GXMSS.IntervalMerkle.root P I pp xs fillers, pp⟩ e msg sig = true) :
    ∃ word : IncomparableEncoding.Codeword v (2 ^ w),
      enc.value pp msg sig.randomizer e = some word ∧
      let ys := fun i => P.chain pp e i (word i) (2 ^ w - 1 - (word i).val) (sig.ots i)
      FrontierPreimage P I pp e he ys sig.path fillers ∨
        ∃ q first second, ∃ address : Fin (h + 1) × Fin (2 ^ h),
          let (subtreeHeight, subtreeIndex) := address
          findAboveFrontier P I pp xs fillers e ys sig.path = some (q, first, second) ∧
          subtreeHeight.val = GXMSS.IntervalMerkle.frontierLevel I e + q ∧
          subtreeIndex.val = e.val / 2 ^ (GXMSS.IntervalMerkle.frontierLevel I e + q) ∧
          GXMSS.IntervalMerkle.frontierLevel I e < subtreeHeight.val ∧
          first = PerfectMerkleTree.honestChildren
            (fun i => GXMSS.IntervalMerkle.subtreeRoot P I pp xs fillers
              (GXMSS.IntervalMerkle.frontierLevel I e) i)
            (fun j i => GXMSS.IntervalMerkle.node P I pp fillers
              (GXMSS.IntervalMerkle.frontierLevel I e + j) i)
            q ((e.val / 2 ^ GXMSS.IntervalMerkle.frontierLevel I e) / 2 ^ q) ∧
          (GXMSS.Security.HashCollision.mk (P.treeTweak address)
            (P.pairInput first) (P.pairInput second)).Sound P.thf pp ∧
          (P.treeTweak address, P.pairInput first) ∈
            honestTargetQueries P I pp xs fillers := by
  obtain ⟨word, hw, hroot⟩ := accepted_opening P enc I pp xs fillers e msg sig hv
  exact ⟨word, hw, inactive_opening_decomposition P I pp xs fillers e he
    (fun i => P.chain pp e i (word i) (2 ^ w - 1 - (word i).val) (sig.ots i))
    sig.path hroot⟩

/-- Equal-frontier raw branch without any complete endpoint array. -/
@[expose] def openingFrontierPreimage [DecidableEq H]
    (P : HashInstance PP T X H h w v) (I : Interval h) (pp : PP)
    (fillers : Fillers I H) (e : Fin (2 ^ h)) (he : ¬ Epoch.IsActive I e)
    (ys : Fin v → H) (auth : Fin h → H) : Option (Sum (Fin v → H) (H × H)) :=
  if openingFrontierDigest P I pp e ys auth = fillers (frontierOf I e he) then
    if hz : frontierLevel I e = 0 then some (.inl ys)
    else some (.inr (openingFrontierPair P I pp e he (Nat.pos_of_ne_zero hz) ys auth))
  else none

/-- Every complete endpoint array has the same raw-preimage projection. -/
theorem openingFrontierPreimage_eq_projection [DecidableEq H]
    (P : HashInstance PP T X H h w v) (I : Interval h) (pp : PP)
    (xs : Fin (2 ^ h) → Fin v → H) (fillers : Fillers I H) (e : Fin (2 ^ h))
    (he : ¬ Epoch.IsActive I e) (ys : Fin v → H) (auth : Fin h → H) :
    openingFrontierPreimage P I pp fillers e he ys auth =
      (match extractInactiveOpening P I pp xs fillers e he ys auth with
      | .inl raw => some raw
      | .inr _ => none) := by
  by_cases hd : openingFrontierDigest P I pp e ys auth = fillers (frontierOf I e he)
  · by_cases hz : frontierLevel I e = 0 <;>
      simp [openingFrontierPreimage, extractInactiveOpening, frontierValue, frontierOf,
        hz] at hd ⊢ <;> simp_all
  · simp [openingFrontierPreimage, extractInactiveOpening, frontierValue, frontierOf] at hd ⊢
    simp_all

/-- Every payload returned by `openingFrontierPreimage` satisfies `RawFrontierPreimage`. -/
theorem openingFrontierPreimage_sound [DecidableEq H]
    (P : HashInstance PP T X H h w v) (I : Interval h) (pp : PP)
    (fillers : Fillers I H) (e : Fin (2 ^ h)) (he : ¬ Epoch.IsActive I e)
    (ys : Fin v → H) (auth : Fin h → H) (raw : Sum (Fin v → H) (H × H))
    (hr : openingFrontierPreimage P I pp fillers e he ys auth = some raw) :
    RawFrontierPreimage P I pp e he fillers raw := by
  have hd : openingFrontierDigest P I pp e ys auth = fillers (frontierOf I e he) := by
    by_contra hn
    simp [openingFrontierPreimage, hn] at hr
  obtain ⟨returned, hx, hp, _⟩ := extractInactiveOpening_of_equal P I pp (fun _ => ys)
    fillers e he ys auth hd
  have hproj := openingFrontierPreimage_eq_projection P I pp (fun _ => ys)
    fillers e he ys auth
  rw [hx, hr] at hproj
  cases Option.some.inj hproj
  exact hp

end GXMSS.Interval.MerkleWitnesses
