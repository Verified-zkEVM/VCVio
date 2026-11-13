/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Chain
public import HashSig.GXMSS.Security.Auxiliary.HashWitnesses
public import VCVio.Algorithms.IndexedChain.Witnesses
public import VCVio.CryptoFoundations.IncomparableEncoding.Code

/-!
# GXMSS chain merge and cut adapters

The shared finite witnesses use one complete GXMSS link as their callback. Position j invokes
paper step j+1, retaining every total-chain extension and the original first-witness order.
-/

public section
namespace GXMSS.HashInstance
open GXMSS.Security
variable {PP T X H : Type} {h w v : ℕ}

/-- Iterating complete links agrees with the admitted total chain operation. -/
private theorem indexedChain_eq (P : HashInstance PP T X H h w v) (pp : PP)
    (e : Fin (2 ^ h)) (i : Fin v) (k n : ℕ) (x : H) :
    VCVio.Algorithms.IndexedChain.chain (fun j y => P.chain pp e i j 1 y) k n x =
      P.chain pp e i k n x := by
  induction n with
  | zero => simp only [VCVio.Algorithms.IndexedChain.chain_zero, HashInstance.chain_zero]
  | succ n ih =>
    rw [VCVio.Algorithms.IndexedChain.chain_succ, ih,
      ← HashInstance.chain_add P pp e i k n 1 x]

/-- Search predecessor offsets through the shared first-merging-pair witness. -/
@[expose] def findChainCollision [DecidableEq H] (P : HashInstance PP T X H h w v)
    (pp : PP) (e : Fin (2 ^ h)) (i : Fin v) (k n : ℕ) (x y : H) : Option (Fin n) :=
  VCVio.Algorithms.IndexedChain.findMerge (fun j z => P.chain pp e i j 1 z) k n x y

/-- The actual returned offset has unequal predecessor values and equal next values. -/
theorem findChainCollision_sound [DecidableEq H] (P : HashInstance PP T X H h w v)
    (pp : PP) (e : Fin (2 ^ h)) (i : Fin v) (k n : ℕ) (x y : H) {d : Fin n}
    (hd : P.findChainCollision pp e i k n x y = some d) :
    P.chain pp e i k d x ≠ P.chain pp e i k d y ∧
      P.chain pp e i k (d.val + 1) x = P.chain pp e i k (d.val + 1) y := by
  simpa only [indexedChain_eq] using VCVio.Algorithms.IndexedChain.findMerge_sound
    (fun j z => P.chain pp e i j 1 z) k n x y hd

/-- Unequal starts with equal endpoints force success of the shared finite search. -/
theorem findChainCollision_isSome [DecidableEq H] (P : HashInstance PP T X H h w v)
    (pp : PP) (e : Fin (2 ^ h)) (i : Fin v) (k n : ℕ) (x y : H)
    (hne : x ≠ y) (heq : P.chain pp e i k n x = P.chain pp e i k n y) :
    (P.findChainCollision pp e i k n x y).isSome := by
  apply VCVio.Algorithms.IndexedChain.findMerge_isSome
    (fun j z => P.chain pp e i j 1 z) k n x y hne
  simpa only [indexedChain_eq] using heq

/-- The adapter keeps exactly the original increasing finite scan, including its first result. -/
theorem findChainCollision_eq_find? [DecidableEq H]
    (P : HashInstance PP T X H h w v) (pp : PP) (e : Fin (2 ^ h)) (i : Fin v)
    (k n : ℕ) (x y : H) : P.findChainCollision pp e i k n x y =
      (List.finRange n).find? (fun d : Fin n => decide
        (P.chain pp e i k d x ≠ P.chain pp e i k d y ∧
          P.chain pp e i k (d.val + 1) x = P.chain pp e i k (d.val + 1) y)) := by
  simp only [findChainCollision, VCVio.Algorithms.IndexedChain.findMerge,
    Fin.find?_eq_find?_finRange, indexedChain_eq]

/-- A legal returned step transports to an oriented collision in the common hash domain. -/
theorem findChainCollision_hash_sound [DecidableEq H]
    (P : HashInstance PP T X H h w v) (pp : PP) (e : Fin (2 ^ h)) (i : Fin v)
    (k n : ℕ) (x y : H) (hbound : k + n ≤ 2 ^ w - 1) {d : Fin n}
    (hd : P.findChainCollision pp e i k n x y = some d) :
    (HashCollision.mk (P.chainTweak (e, i, ⟨k + d.val, by omega⟩))
      (P.digestInput (P.chain pp e i k d x))
      (P.digestInput (P.chain pp e i k d y))).Sound P.thf pp := by
  obtain ⟨hne, heq⟩ := P.findChainCollision_sound pp e i k n x y hd
  apply collision_embedding _ _ _ _ hne
  simpa only [P.chain_succ pp e i k d x (by omega),
    P.chain_succ pp e i k d y (by omega)] using heq

/-- The shared cut witness returns the original predecessor or post-cut merging offset. -/
@[expose] def findChainCut [DecidableEq H] (P : HashInstance PP T X H h w v)
    (pp : PP) (e : Fin (2 ^ h)) (i : Fin v) (t s b : ℕ) (x y : H) :
    Option (H ⊕ Fin (b - s)) :=
  VCVio.Algorithms.IndexedChain.findCut (fun j z => P.chain pp e i j 1 z) t s b x y

/-- The cut adapter retains the exact original test, predecessor and oriented merge branch. -/
theorem findChainCut_eq [DecidableEq H] (P : HashInstance PP T X H h w v)
    (pp : PP) (e : Fin (2 ^ h)) (i : Fin v) (t s b : ℕ) (x y : H) :
    P.findChainCut pp e i t s b x y =
      if P.chain pp e i t (s - t) y = x then
        some (.inl (P.chain pp e i t (s - t - 1) y))
      else
        (P.findChainCollision pp e i s (b - s) x (P.chain pp e i t (s - t) y)).map Sum.inr := by
  simp only [findChainCut, VCVio.Algorithms.IndexedChain.findCut, indexedChain_eq,
    findChainCollision]

/-- A legal preimage branch hashes to the selected value at paper step s. -/
theorem findChainCut_preimage_sound [DecidableEq H] (P : HashInstance PP T X H h w v)
    (pp : PP) (e : Fin (2 ^ h)) (i : Fin v) (t s b : ℕ) (x y u : H)
    (hts : t < s) (hs : s ≤ 2 ^ w - 1)
    (hu : P.findChainCut pp e i t s b x y = some (.inl u)) :
    (HashInstance.thf P).eval pp (P.chainTweak (e, i, ⟨s - 1, by omega⟩))
      (P.digestInput u) = x := by
  have h := VCVio.Algorithms.IndexedChain.findCut_preimage_sound
    (fun j z => P.chain pp e i j 1 z) t s b x y u hts hu
  change P.chain pp e i (s - 1) 1 u = x at h
  rw [HashInstance.chain_succ P pp e i (s - 1) 0 u (by omega),
    HashInstance.chain_zero] at h
  simpa only [Nat.add_zero] using h

/-- The merge branch retains the trajectory beginning at the selected cut as its first input. -/
theorem findChainCut_collision_sound [DecidableEq H]
    (P : HashInstance PP T X H h w v) (pp : PP) (e : Fin (2 ^ h)) (i : Fin v)
    (t s b : ℕ) (x y : H) {d : Fin (b - s)}
    (hd : P.findChainCut pp e i t s b x y = some (.inr d)) :
    P.findChainCollision pp e i s (b - s) x (P.chain pp e i t (s - t) y) = some d := by
  simpa only [findChainCollision, indexedChain_eq] using
    VCVio.Algorithms.IndexedChain.findCut_merge_sound
    (fun j z => P.chain pp e i j 1 z) t s b x y hd

/-- Equal endpoints across a legal cut force one of the two shared witness branches. -/
theorem findChainCut_isSome [DecidableEq H] (P : HashInstance PP T X H h w v)
    (pp : PP) (e : Fin (2 ^ h)) (i : Fin v) (t s b : ℕ) (x y : H)
    (hts : t < s) (hsb : s ≤ b)
    (heq : P.chain pp e i s (b - s) x = P.chain pp e i t (b - t) y) :
    (P.findChainCut pp e i t s b x y).isSome := by
  apply VCVio.Algorithms.IndexedChain.findCut_isSome
    (fun j z => P.chain pp e i j 1 z) t s b x y hts hsb
  simpa only [indexedChain_eq] using heq

/-- A cut collision is a legal same-tweak collision strictly above the designated cut. -/
theorem findChainCut_hash_sound [DecidableEq H]
    (P : HashInstance PP T X H h w v) (pp : PP) (e : Fin (2 ^ h)) (i : Fin v)
    (t s b : ℕ) (x y : H) (hsb : s ≤ b) (hb : b ≤ 2 ^ w - 1)
    {d : Fin (b - s)} (hd : P.findChainCut pp e i t s b x y = some (.inr d)) :
    (HashCollision.mk (P.chainTweak (e, i, ⟨s + d.val, by omega⟩))
      (P.digestInput (P.chain pp e i s d x))
      (P.digestInput (P.chain pp e i s d (P.chain pp e i t (s - t) y)))).Sound
        P.thf pp :=
  P.findChainCollision_hash_sound pp e i s (b - s) x _ (by omega)
    (P.findChainCut_collision_sound pp e i t s b x y hd)

/-- A zero-span aligned collision premise with distinct starts is impossible. -/
theorem chain_zero_ne (P : HashInstance PP T X H h w v) (pp : PP)
    (e : Fin (2 ^ h)) (i : Fin v) (k : ℕ) {x y : H} (hne : x ≠ y) :
    P.chain pp e i k 0 x ≠ P.chain pp e i k 0 y := by
  simpa using hne

/-- At an endpoint cut, a verifying earlier trajectory returns its predecessor at that cut. -/
theorem findChainCut_endpoint [DecidableEq H] (P : HashInstance PP T X H h w v)
    (pp : PP) (e : Fin (2 ^ h)) (i : Fin v) (t s : ℕ) (x y : H)
    (heq : x = P.chain pp e i t (s - t) y) :
    P.findChainCut pp e i t s s x y = some (.inl (P.chain pp e i t (s - t - 1) y)) := by
  simp [findChainCut_eq, heq]

/-- The paper endpoint is obtained without any hypothesis beyond the cut and endpoint equality. -/
theorem findChainCut_isSome_at_max [DecidableEq H] (P : HashInstance PP T X H h w v)
    (pp : PP) (e : Fin (2 ^ h)) (i : Fin v) (t s : ℕ) (x y : H)
    (hts : t < s) (hs : s ≤ 2 ^ w - 1)
    (heq : P.chain pp e i s (2 ^ w - 1 - s) x =
      P.chain pp e i t (2 ^ w - 1 - t) y) :
    (P.findChainCut pp e i t s (2 ^ w - 1) x y).isSome :=
  P.findChainCut_isSome pp e i t s (2 ^ w - 1) x y hts hs heq

/-- The computed smaller codeword coordinate directly supplies the designated-cut witness.
Global incomparability supplies finder success separately through successful encoding laws. -/
theorem findChainCut_isSome_of_smallerCoordinate [DecidableEq H]
    (P : HashInstance PP T X H h w v) (pp : PP) (e : Fin (2 ^ h))
    (x y : IncomparableEncoding.Codeword v (2 ^ w)) {i : Fin v}
    (hi : Fin.find? (fun j => decide ((y j).val < (x j).val)) = some i) (u z : H)
    (heq : P.chain pp e i (x i) (2 ^ w - 1 - (x i).val) u =
      P.chain pp e i (y i) (2 ^ w - 1 - (y i).val) z) :
    (P.findChainCut pp e i (y i) (x i) (2 ^ w - 1) u z).isSome := by
  have hlt : (y i).val < (x i).val :=
    of_decide_eq_true (Fin.eq_true_of_find?_eq_some hi)
  apply P.findChainCut_isSome_at_max pp e i (y i) (x i) u z hlt _ heq
  have hb := (x i).isLt
  omega

end GXMSS.HashInstance
