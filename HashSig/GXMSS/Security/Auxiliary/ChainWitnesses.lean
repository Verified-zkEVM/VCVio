/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Auxiliary.HashWitnesses
public import HashSig.GXMSS.Chain

/-!
# Bounded collision and designated-cut chain witnesses

The first trajectory is designated honest. Positive paper step `k+d+1` uses finite
coordinate `k+d`. The cut computation never needs the honest predecessor below the cut.
-/

public section

namespace GXMSS.HashInstance

open Security

variable {PP T X H : Type} {h w v : ℕ}

/-- Scan predecessor offsets for an unequal pair that merges on the next call. -/
@[expose] def findChainCollision [DecidableEq H] (P : HashInstance PP T X H h w v)
    (pp : PP) (e : Fin (2 ^ h)) (i : Fin v) (k n : ℕ) (x y : H) : Option (Fin n) :=
  findCoordinate (fun d => P.chain pp e i k d x ≠ P.chain pp e i k d y ∧
    P.chain pp e i k (d.val + 1) x = P.chain pp e i k (d.val + 1) y)

/-- A returned offset identifies the two trajectories immediately before and after merging. -/
theorem findChainCollision_sound [DecidableEq H] (P : HashInstance PP T X H h w v)
    (pp : PP) (e : Fin (2 ^ h)) (i : Fin v) (k n : ℕ) (x y : H) {d : Fin n}
    (hd : P.findChainCollision pp e i k n x y = some d) :
    P.chain pp e i k d x ≠ P.chain pp e i k d y ∧
      P.chain pp e i k (d.val + 1) x = P.chain pp e i k (d.val + 1) y :=
  findCoordinate_sound _ hd

private theorem exists_chain_merge (P : HashInstance PP T X H h w v)
    (pp : PP) (e : Fin (2 ^ h)) (i : Fin v) (k n : ℕ) (x y : H)
    (hne : x ≠ y) (heq : P.chain pp e i k n x = P.chain pp e i k n y) :
    ∃ d : Fin n, P.chain pp e i k d x ≠ P.chain pp e i k d y ∧
      P.chain pp e i k (d.val + 1) x = P.chain pp e i k (d.val + 1) y := by
  induction n with
  | zero => exact (hne (by simpa using heq)).elim
  | succ n ih =>
    rcases Classical.em (P.chain pp e i k n x = P.chain pp e i k n y) with hprev | hprev
    · obtain ⟨d, hd⟩ := ih hprev
      exact ⟨⟨d.val, by omega⟩, hd⟩
    · exact ⟨⟨n, by omega⟩, hprev, heq⟩

/-- Unequal starts with equal endpoints force a returned merging offset. -/
theorem findChainCollision_isSome [DecidableEq H] (P : HashInstance PP T X H h w v)
    (pp : PP) (e : Fin (2 ^ h)) (i : Fin v) (k n : ℕ) (x y : H)
    (hne : x ≠ y) (heq : P.chain pp e i k n x = P.chain pp e i k n y) :
    (P.findChainCollision pp e i k n x y).isSome :=
  findCoordinate_isSome _ (exists_chain_merge P pp e i k n x y hne heq)

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

/-- Either a forged predecessor at the cut, or a merging offset strictly after the cut. -/
@[expose] def findChainCut [DecidableEq H] (P : HashInstance PP T X H h w v)
    (pp : PP) (e : Fin (2 ^ h)) (i : Fin v) (t s b : ℕ) (x y : H) :
    Option (H ⊕ Fin (b - s)) :=
  if P.chain pp e i t (s - t) y = x then
    some (.inl (P.chain pp e i t (s - t - 1) y))
  else
    (P.findChainCollision pp e i s (b - s) x (P.chain pp e i t (s - t) y)).map Sum.inr

/-- The preimage branch evaluates to the designated honest value at paper step `s`. -/
theorem findChainCut_preimage_sound [DecidableEq H] (P : HashInstance PP T X H h w v)
    (pp : PP) (e : Fin (2 ^ h)) (i : Fin v) (t s b : ℕ) (x y u : H)
    (hts : t < s) (hs : s ≤ 2 ^ w - 1)
    (hu : P.findChainCut pp e i t s b x y = some (.inl u)) :
  (HashInstance.thf P).eval pp (P.chainTweak (e, i, ⟨s - 1, by omega⟩)) (P.digestInput u) = x := by
  unfold findChainCut at hu
  split at hu
  next heq =>
    have hu' : P.chain pp e i t (s - t - 1) y = u := by simpa using hu
    have hoff : t + (s - t - 1) = s - 1 := by omega
    have hlen : s - t - 1 + 1 = s - t := by omega
    have hstep := P.chain_succ pp e i t (s - t - 1) y (by omega)
    simpa [hoff, hlen, hu', heq] using hstep.symm
  next hne => simp at hu

/-- The collision branch retains the honest trajectory at the designated cut. -/
theorem findChainCut_collision_sound [DecidableEq H]
    (P : HashInstance PP T X H h w v) (pp : PP) (e : Fin (2 ^ h)) (i : Fin v)
    (t s b : ℕ) (x y : H) {d : Fin (b - s)}
    (hd : P.findChainCut pp e i t s b x y = some (.inr d)) :
    P.findChainCollision pp e i s (b - s) x (P.chain pp e i t (s - t) y) = some d := by
  unfold findChainCut at hd
  split at hd
  · simp at hd
  · simpa using hd

/-- Equal endpoints force one of the two computable designated-cut witnesses. -/
theorem findChainCut_isSome [DecidableEq H] (P : HashInstance PP T X H h w v)
    (pp : PP) (e : Fin (2 ^ h)) (i : Fin v) (t s b : ℕ) (x y : H)
    (hts : t < s) (hsb : s ≤ b)
    (heq : P.chain pp e i s (b - s) x = P.chain pp e i t (b - t) y) :
    (P.findChainCut pp e i t s b x y).isSome := by
  unfold findChainCut
  split
  · rfl
  next hne =>
    simp only [Option.isSome_map]
    apply P.findChainCollision_isSome pp e i s (b - s) x _ (Ne.symm hne)
    have hcomp := P.chain_add pp e i t (s - t) (b - s) y
    have hstart : t + (s - t) = s := by omega
    have hlen : s - t + (b - s) = b - t := by omega
    rw [hstart, hlen] at hcomp
    exact heq.trans hcomp

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
  simp [findChainCut, heq]

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
    (x y : Encoding.Codeword v (2 ^ w)) {i : Fin v}
    (hi : findSmallerCoordinate x y = some i) (u z : H)
    (heq : P.chain pp e i (x i) (2 ^ w - 1 - (x i).val) u =
      P.chain pp e i (y i) (2 ^ w - 1 - (y i).val) z) :
    (P.findChainCut pp e i (y i) (x i) (2 ^ w - 1) u z).isSome := by
  have hlt : (y i).val < (x i).val :=
    findSmallerCoordinate_sound x y hi
  apply P.findChainCut_isSome_at_max pp e i (y i) (x i) u z hlt _ heq
  have hb := (x i).isLt
  omega

end GXMSS.HashInstance
