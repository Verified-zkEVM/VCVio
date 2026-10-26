/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Bridge.Encodings
public import HashSig.SLHDSA.SHAKE128s.Bridge.Transfer
import Mathlib.Data.Nat.Bitwise
import VCVio.CryptoFoundations.MerkleTree.Addressed.NatIndexed.Option

/-!
# FORS of the paper model is FORS of FIPS 205 over one oracle

Each FORS program of the paper model (`HashSig.SLHDSA.SHAKE128s.Statement.Scheme`), run in the
FIPS 205 single-oracle world through `relabel answerEquiv`, is the corresponding program of FIPS
205's library (`HashSig.SLHDSA.Fors`, `HashSig.SLHDSA.SecretProvider`) over the typed interface
`unifSpec + hashSpec FIPS205.core`, run through `encImpl FIPS205.params`, with its output read
back as paper values. The two programs issue the same single-oracle queries in the same order.
Inputs are related by `digestEquiv` (seeds and nodes) and `toAdrs` (addresses); the secret values
come from the provider `oracleSecret FIPS205.core (Equiv.refl _)` that `romScheme` signs with.

## Main statements

* `simulateQ_forsSecret`: `Fors.secret` is the provider at `forsSkAdrs`.
* `simulateQ_forsLeaf`, `simulateQ_forsNode`, `simulateQ_forsRoot`: `Fors.node` is
  `forsLeafWithSecret` at height `0`, `merkleRootM` over it at every height, and
  `forsRootWithSecret` at the tree roots.
* `simulateQ_forsAuthPath`: the paper's authentication path of a leaf is `intrinsicAuthPathM`.
* `simulateQ_forsSign`: `Fors.sign` is `forsSignWithSecretM`; both draw each tree's selected
  secret before its authentication path, as FIPS 205 Algorithm 16 orders them.
* `simulateQ_forsPublicKeyFromSignature`: `Fors.publicKeyFromSignature` is `forsPkFromSigM`.
* The `*_parts` forms state the signing and recovery equalities at the digest split of an
  `H_msg` answer, as the schemes use them.

## Implementation notes

The tweakable-hash equalities (`ForsBridge.simulateQ_tweakable_tl` and its `F` and `H` forms)
hold at any FIPS 205 address whose bytes are the paper address's bytes.
-/

public section

open OracleComp OracleSpec

namespace SLHDSA.SHAKE128s.Bridge

open SLHDSA SLHDSA.Security

/-- The typed interface of FIPS 205's random-oracle scheme at SLH-DSA-SHAKE-128s. -/
local notation "TypedWorld" => unifSpec + hashSpec FIPS205.core

/-- Run a paper program in the FIPS 205 single-oracle world. -/
local notation "𝓡" => simulateQ (relabel answerEquiv)

/-- Run a program of the typed interface in the FIPS 205 single-oracle world. -/
local notation "𝓔" => simulateQ (encImpl FIPS205.params)

namespace ForsBridge

/-! ## One tweakable-hash query -/

/-- One query of the FIPS 205 single oracle. -/
abbrev ask (x : Bytes) : OracleComp (Game.World FIPS205.Answer) FIPS205.Answer :=
  liftM ((Game.World FIPS205.Answer).query (.inr x))

/-- A relabelled paper tweakable hash asks the oracle at the paper's input and truncates the
answer, read back as a paper value. -/
theorem simulateQ_relabel_tweakable (seed : Digest) (a : Address) (payload : Bytes) :
    𝓡 (Hashing.tweakable seed a payload : OracleComp OracleWorld Digest) =
      (fun h => Hashing.truncate (answerEquiv.symm h)) <$>
        ask (Hashing.tweakableInput seed a payload) := by
  change Hashing.truncate <$> 𝓡
    (liftM (OracleWorld.query (.inr (Hashing.tweakableInput seed a payload))) :
      OracleComp OracleWorld HashOutput) = _
  rw [simulateQ_spec_query, relabel_apply_inr, Functor.map_map]

/-- An encoded `T_l` query asks the oracle at its FIPS 205 layout and reads the first `n` bytes. -/
theorem simulateQ_encImpl_tl (pk : FIPS205.core.PkSeed) (A : Adrs) (xs : List FIPS205.core.Y) :
    𝓔 (PublicHash.tl FIPS205.core pk A xs : OracleComp TypedWorld FIPS205.core.Y) =
      prefixBytes FIPS205.params.params.n <$>
        ask (encode FIPS205.params (.inl (.thash pk (FIPS205.core.adrsToKey A) xs))) := by
  change 𝓔 (liftM ((TypedWorld).query (.inr (.inl (.thash pk (FIPS205.core.adrsToKey A) xs)))) :
      OracleComp TypedWorld FIPS205.core.Y) = _
  rw [simulateQ_spec_query]
  rfl

/-- **One tweakable hash**: the paper's tweakable hash of digests at `a` is FIPS 205's `T_l` of
their nodes at any address `A` with the bytes of `a`. -/
theorem simulateQ_tweakable_tl (seed : Digest) (a : Address) {A : Adrs}
    (hA : A.toBytes = a.toBytes) (xs : List Digest) :
    𝓡 (Hashing.tweakable seed a (xs.map (bytesBE n)).flatten : OracleComp OracleWorld Digest) =
      digestEquiv.symm <$>
        𝓔 (PublicHash.tl FIPS205.core (digestEquiv seed) A (xs.map digestEquiv) :
          OracleComp TypedWorld FIPS205.core.Y) := by
  have hE := simulateQ_encImpl_tl (digestEquiv seed) A (xs.map digestEquiv)
  rw [encode_thash seed hA xs] at hE
  rw [simulateQ_relabel_tweakable, hE]
  refine Eq.trans ?_ (Functor.map_map (prefixBytes FIPS205.params.params.n) digestEquiv.symm
    (ask (Hashing.tweakableInput seed a (List.map (bytesBE n) xs).flatten))).symm
  congr 1
  funext h
  have hp := prefixBytes_answerEquiv (answerEquiv.symm h)
  rw [Equiv.apply_symm_apply] at hp
  exact (digestEquiv.symm_apply_eq.mpr hp).symm

/-- `simulateQ_tweakable_tl` for one input: FIPS 205's `F`. -/
theorem simulateQ_tweakable_f (seed : Digest) (a : Address) {A : Adrs}
    (hA : A.toBytes = a.toBytes) (x : Digest) :
    𝓡 (Hashing.tweakable seed a (bytesBE n x) : OracleComp OracleWorld Digest) =
      digestEquiv.symm <$>
        𝓔 (PublicHash.f FIPS205.core (digestEquiv seed) A (digestEquiv x) :
          OracleComp TypedWorld FIPS205.core.Y) := by
  have h := simulateQ_tweakable_tl seed a hA [x]
  simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
    List.append_nil] at h
  exact h

/-- `simulateQ_tweakable_tl` for two inputs: FIPS 205's `H`. -/
theorem simulateQ_tweakable_h (seed : Digest) (a : Address) {A : Adrs}
    (hA : A.toBytes = a.toBytes) (l r : Digest) :
    𝓡 (Hashing.tweakable seed a (bytesBE n l ++ bytesBE n r) : OracleComp OracleWorld Digest) =
      digestEquiv.symm <$>
        𝓔 (PublicHash.h FIPS205.core (digestEquiv seed) A (digestEquiv l) (digestEquiv r) :
          OracleComp TypedWorld FIPS205.core.Y) := by
  have h := simulateQ_tweakable_tl seed a hA [l, r]
  simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
    List.append_nil] at h
  exact h

/-! ## Composing correspondences -/

/-- Correspondences compose along `bind`: if `P` corresponds to `V` through `c` and each
continuation `Q (c y)` to `W y` through `d`, then `P >>= Q` corresponds to `V >>= W`. -/
theorem bind_bridge {α β γ δ : Type} {P : OracleComp OracleWorld α}
    {Q : α → OracleComp OracleWorld β} {V : OracleComp TypedWorld γ}
    {W : γ → OracleComp TypedWorld δ} {c : γ → α} {d : δ → β}
    (hP : 𝓡 P = c <$> 𝓔 V) (hQ : ∀ y, 𝓡 (Q (c y)) = d <$> 𝓔 (W y)) :
    𝓡 (P >>= Q) = d <$> 𝓔 (V >>= W) := by
  rw [simulateQ_bind, hP, bind_map_left, simulateQ_bind, map_bind]
  exact bind_congr hQ

/-- Pure values correspond when the conversion maps one to the other. -/
theorem pure_bridge {α β : Type} (x : α) (y : β) (c : β → α) (h : c y = x) :
    𝓡 (pure x : OracleComp OracleWorld α) = c <$> 𝓔 (pure y : OracleComp TypedWorld β) := by
  simp [h]

/-- Correspondences compose along the paper's `sequenceFin` and FIPS 205's `Vector.ofFnM`. -/
theorem sequenceFin_bridge {α β : Type} {k : ℕ} (P : Fin k → OracleComp OracleWorld α)
    (V : Fin k → OracleComp TypedWorld β) (c : β → α)
    (h : ∀ i, 𝓡 (P i) = c <$> 𝓔 (V i)) :
    𝓡 (sequenceFin k P) = (fun v i => c v[i]) <$> 𝓔 (Vector.ofFnM V) := by
  induction k with
  | zero =>
    rw [sequenceFin, Vector.ofFnM_zero]
    exact pure_bridge _ _ _ (funext fun i => i.elim0)
  | succ k ih =>
    rw [sequenceFin, Vector.ofFnM_succ']
    refine bind_bridge (h 0) fun y => ?_
    refine bind_bridge (ih _ _ fun i => h i.succ) fun v => ?_
    refine pure_bridge _ _ _ (funext fun i => ?_)
    induction i using Fin.cases with
    | zero => simp
    | succ i => simp [Vector.getElem_append_right]

/-- Correspondences compose along left folds of node-valued steps. -/
theorem foldlM_bridge {ι : Type} (l : List ι) (f : Digest → ι → OracleComp OracleWorld Digest)
    (g : FIPS205.core.Y → ι → OracleComp TypedWorld FIPS205.core.Y)
    (h : ∀ y j, 𝓡 (f (digestEquiv.symm y) j) = digestEquiv.symm <$> 𝓔 (g y j))
    (y : FIPS205.core.Y) :
    𝓡 (l.foldlM f (digestEquiv.symm y)) = digestEquiv.symm <$> 𝓔 (l.foldlM g y) := by
  induction l generalizing y with
  | nil => exact pure_bridge _ _ _ rfl
  | cons j l ih =>
    rw [List.foldlM_cons, List.foldlM_cons]
    exact bind_bridge (h y j) ih

/-! ## Merkle programs -/

/-- An intrinsic authentication path is the vector of the sibling roots, level by level. -/
theorem intrinsicAuthPathM_eq_ofFnM {Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (leaf : ℕ → m Y) (nodeHash : ℕ → ℕ → Y → Y → m Y) (idx z : ℕ) :
    PerfectMerkleTree.intrinsicAuthPathM leaf nodeHash idx z =
      Vector.ofFnM fun j : Fin z => PerfectMerkleTree.merkleRootM leaf nodeHash j.val
        (PerfectMerkleTree.sibling (idx / 2 ^ j.val)) := by
  induction z with
  | zero => simp [PerfectMerkleTree.intrinsicAuthPathM]
  | succ z ih => simp [PerfectMerkleTree.intrinsicAuthPathM, Vector.ofFnM_succ, ih]

/-- `climbM` along a path given as a function of the level is a left fold over the levels. -/
theorem climbM_ofFn {Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (nodeHash : ℕ → ℕ → Y → Y → m Y) (idx : ℕ) (node : Y) {z : ℕ} (g : Fin z → Y) :
    PerfectMerkleTree.climbM nodeHash idx node (List.ofFn g) =
      (List.finRange z).foldlM (fun v j =>
        if idx / 2 ^ j.val % 2 = 0 then nodeHash (j.val + 1) (idx / 2 ^ (j.val + 1)) v (g j)
        else nodeHash (j.val + 1) (idx / 2 ^ (j.val + 1)) (g j) v) node := by
  induction z with
  | zero => simp
  | succ z ih =>
    rw [List.ofFn_succ_last, PerfectMerkleTree.climbM_concat, ih, List.finRange_succ_last,
      List.foldlM_append, List.foldlM_map]
    simp

/-- `climbM` along the entries of a vector is a left fold over the levels. -/
theorem climbM_toList {Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (nodeHash : ℕ → ℕ → Y → Y → m Y) (idx : ℕ) (node : Y) {z : ℕ} (v : Vector Y z) :
    PerfectMerkleTree.climbM nodeHash idx node v.toList =
      (List.finRange z).foldlM (fun x j =>
        if idx / 2 ^ j.val % 2 = 0 then nodeHash (j.val + 1) (idx / 2 ^ (j.val + 1)) x v[j]
        else nodeHash (j.val + 1) (idx / 2 ^ (j.val + 1)) v[j] x) node := by
  rw [← climbM_ofFn]
  congr 1
  apply List.ext_getElem <;> simp

/-! ## Index arithmetic -/

/-- `xor 1` is the Merkle sibling. -/
theorem xor_one_eq_sibling (q : ℕ) : Nat.xor q 1 = PerfectMerkleTree.sibling q := by
  unfold PerfectMerkleTree.sibling
  change q ^^^ 1 = _
  rcases Nat.even_or_odd q with h | h
  · rw [Nat.xor_one_of_even h, ite_eq_left (Nat.even_iff.mp h)]
  · rw [Nat.xor_one_of_odd h, ite_eq_right (by have := Nat.odd_iff.mp h; omega)]

/-- The height-`j` ancestor of global leaf `i * 2 ^ H + leaf` is node
`i * 2 ^ (H - j) + leaf / 2 ^ j`. -/
theorem global_div_pow {H j : ℕ} (hj : j ≤ H) (i leaf : ℕ) :
    (i * 2 ^ H + leaf) / 2 ^ j = i * 2 ^ (H - j) + leaf / 2 ^ j := by
  have : i * 2 ^ H = i * 2 ^ (H - j) * 2 ^ j := by
    rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hj]
  rw [this, add_comm, Nat.add_mul_div_right _ _ (by positivity), add_comm]

/-- The sibling of the height-`j` ancestor of global leaf `i * 2 ^ H + leaf` is the paper's
`i * 2 ^ (H - j) + (leaf / 2 ^ j xor 1)`. -/
theorem sibling_global {H j : ℕ} (hj : j < H) (i leaf : ℕ) :
    PerfectMerkleTree.sibling ((i * 2 ^ H + leaf) / 2 ^ j) =
      i * 2 ^ (H - j) + Nat.xor (leaf / 2 ^ j) 1 := by
  rw [global_div_pow hj.le, xor_one_eq_sibling]
  have hpow : 2 ^ (H - j) = 2 * 2 ^ (H - j - 1) := by
    rw [← pow_succ']; congr 1; omega
  rw [hpow, show i * (2 * 2 ^ (H - j - 1)) = 2 * (i * 2 ^ (H - j - 1)) by ring]
  unfold PerfectMerkleTree.sibling
  generalize leaf / 2 ^ j = q
  generalize i * 2 ^ (H - j - 1) = c
  split_ifs <;> omega

/-- The sibling of a node below `2 ^ h` stays below `2 ^ h`, for `h > 0`. -/
theorem xor_one_lt_pow {q h : ℕ} (hh : 0 < h) (hq : q < 2 ^ h) : Nat.xor q 1 < 2 ^ h := by
  rw [xor_one_eq_sibling]
  have hpow : 2 ^ h = 2 * 2 ^ (h - 1) := by rw [← pow_succ']; congr 1; omega
  unfold PerfectMerkleTree.sibling
  split_ifs <;> omega

/-- Below the tree root, the parity of the global index's ancestor is that of the local leaf's. -/
theorem global_div_pow_mod_two {i leaf j : ℕ} (hj : j < forsHeight) :
    (i * 2 ^ forsHeight + leaf) / 2 ^ j % 2 = leaf / 2 ^ j % 2 := by
  rw [global_div_pow hj.le]
  have hpow : 2 ^ (forsHeight - j) = 2 * 2 ^ (forsHeight - j - 1) := by
    rw [← pow_succ']; congr 1; omega
  rw [hpow, show i * (2 * 2 ^ (forsHeight - j - 1)) = 2 * (i * 2 ^ (forsHeight - j - 1)) by ring]
  omega

/-- The bytes of an array of digests are the flattened bytes of its list. -/
theorem digestArrayBytes_eq {size : ℕ} (values : Fin size → Digest) :
    digestArrayBytes values = ((List.ofFn values).map (bytesBE n)).flatten := by
  rw [digestArrayBytes, List.map_ofFn]
  rfl

end ForsBridge

open ForsBridge

/-! ## FORS secrets, leaves and nodes -/

/-- FORS-tree node addresses of the two schemes have the same bytes. -/
theorem toBytes_forsNodeAdrs (a : Address) (hk : a.kind = .forsTree) {z t : ℕ}
    (hz : z < 2 ^ 32) (ht : t < 2 ^ 32) :
    (forsNodeAdrs (toAdrs a) z t).toBytes = (Fors.nodeAddress a z t).toBytes := by
  rw [← toAdrs_forsNodeAddress a hk hz ht, toBytes_toAdrs]

/-- **FORS secrets**: the paper's secret at global index `index` is the oracle-secret provider of
`romScheme` at `forsSkAdrs`. -/
theorem simulateQ_forsSecret (sk pk : Digest) (a : Address) {index : ℕ} (hi : index < 2 ^ 32) :
    𝓡 (Fors.secret sk pk a index : OracleComp OracleWorld Digest) =
      digestEquiv.symm <$>
        𝓔 (oracleSecret FIPS205.core (Equiv.refl _) (digestEquiv pk) (digestEquiv sk)
          (forsSkAdrs (toAdrs a) index) : OracleComp TypedWorld FIPS205.core.Y) :=
  simulateQ_tweakable_f pk (Fors.secretAddress a index)
    (by rw [← toAdrs_forsSecretAddress a hi, toBytes_toAdrs]) sk

/-- **FORS leaves**: the paper's height-`0` node is `forsLeafWithSecret`: the secret, then `F` at
the leaf address. -/
theorem simulateQ_forsLeaf (sk pk : Digest) (a : Address) (hk : a.kind = .forsTree) {t : ℕ}
    (ht : t < 2 ^ 32) :
    𝓡 (Fors.node sk pk a 0 t : OracleComp OracleWorld Digest) =
      digestEquiv.symm <$>
        𝓔 (forsLeafWithSecret FIPS205.core (PublicHash.f FIPS205.core (digestEquiv pk))
          (oracleSecret FIPS205.core (Equiv.refl _) (digestEquiv pk) (digestEquiv sk))
          (toAdrs a) t : OracleComp TypedWorld FIPS205.core.Y) := by
  rw [Fors.node]
  refine bind_bridge (simulateQ_forsSecret sk pk a ht) fun y => ?_
  have h := simulateQ_tweakable_f pk (Fors.nodeAddress a 0 t)
    (toBytes_forsNodeAdrs a hk (by norm_num) ht) (digestEquiv.symm y)
  rw [Equiv.apply_symm_apply] at h
  exact h

/-- **FORS nodes**: the paper's node at height `z` and global index `t` is `merkleRootM` over
`forsLeafWithSecret` and `forsNodeHashWith`, whenever the subtree's leaves have indices below
`2 ^ 32`. -/
theorem simulateQ_forsNode (sk pk : Digest) (a : Address) (hk : a.kind = .forsTree)
    (z t : ℕ) (hzt : 2 ^ z * (t + 1) ≤ 2 ^ 32) :
    𝓡 (Fors.node sk pk a z t : OracleComp OracleWorld Digest) =
      digestEquiv.symm <$>
        𝓔 (PerfectMerkleTree.merkleRootM
          (forsLeafWithSecret FIPS205.core (PublicHash.f FIPS205.core (digestEquiv pk))
            (oracleSecret FIPS205.core (Equiv.refl _) (digestEquiv pk) (digestEquiv sk))
            (toAdrs a))
          (forsNodeHashWith (PublicHash.h FIPS205.core (digestEquiv pk)) (toAdrs a)) z t :
          OracleComp TypedWorld FIPS205.core.Y) := by
  induction z generalizing t with
  | zero =>
    exact simulateQ_forsLeaf sk pk a hk (by simpa using hzt)
  | succ z ih =>
    have hpow : 2 ^ (z + 1) = 2 * 2 ^ z := by rw [pow_succ]; ring
    have hz : z + 1 < 2 ^ 32 := by
      have := Nat.lt_two_pow_self (n := z + 1)
      have : 2 ^ (z + 1) ≤ 2 ^ 32 := le_trans (Nat.le_mul_of_pos_right _ (by omega)) hzt
      omega
    have ht : t < 2 ^ 32 := by
      have : t + 1 ≤ 2 ^ (z + 1) * (t + 1) := Nat.le_mul_of_pos_left _ (by positivity)
      omega
    rw [Fors.node, PerfectMerkleTree.merkleRootM]
    refine bind_bridge (ih (2 * t) (by rw [hpow] at hzt; nlinarith)) fun l => ?_
    refine bind_bridge (ih (2 * t + 1) (by rw [hpow] at hzt; nlinarith)) fun r => ?_
    have h := simulateQ_tweakable_h pk (Fors.nodeAddress a (z + 1) t)
      (toBytes_forsNodeAdrs a hk hz ht) (digestEquiv.symm l) (digestEquiv.symm r)
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h
    exact h

/-- **FORS tree roots**: the paper's root of tree `i` is `forsRootWithSecret`. -/
theorem simulateQ_forsRoot (sk pk : Digest) (a : Address) (hk : a.kind = .forsTree)
    (i : Fin forsTrees) :
    𝓡 (Fors.node sk pk a forsHeight i.val : OracleComp OracleWorld Digest) =
      digestEquiv.symm <$>
        𝓔 (forsRootWithSecret FIPS205.core (PublicHash.f FIPS205.core (digestEquiv pk))
          (PublicHash.h FIPS205.core (digestEquiv pk))
          (oracleSecret FIPS205.core (Equiv.refl _) (digestEquiv pk) (digestEquiv sk))
          (toAdrs a) i.val : OracleComp TypedWorld FIPS205.core.Y) := by
  have hi : i.val < 14 := i.isLt
  exact simulateQ_forsNode sk pk a hk forsHeight i.val (by simp only [forsHeight]; omega)

/-! ## FORS signing -/

/-- **FORS authentication paths**: the paper's path of leaf `leaf` in tree `i` is FIPS 205's
intrinsic authentication path of the global leaf `i * 2 ^ a + leaf`. -/
theorem simulateQ_forsAuthPath (sk pk : Digest) (a : Address) (hk : a.kind = .forsTree)
    (i : Fin forsTrees) {leaf : ℕ} (hleaf : leaf < 2 ^ forsHeight) :
    𝓡 (sequenceFin forsHeight (fun j => Fors.node sk pk a j.val
        (i.val * 2 ^ (forsHeight - j.val) + Nat.xor (leaf / 2 ^ j.val) 1)) :
        OracleComp OracleWorld (Fin forsHeight → Digest)) =
      (fun v j => digestEquiv.symm v[j]) <$>
        𝓔 (PerfectMerkleTree.intrinsicAuthPathM
          (forsLeafWithSecret FIPS205.core (PublicHash.f FIPS205.core (digestEquiv pk))
            (oracleSecret FIPS205.core (Equiv.refl _) (digestEquiv pk) (digestEquiv sk))
            (toAdrs a))
          (forsNodeHashWith (PublicHash.h FIPS205.core (digestEquiv pk)) (toAdrs a))
          (i.val * 2 ^ forsHeight + leaf) forsHeight :
          OracleComp TypedWorld (Vector FIPS205.core.Y forsHeight)) := by
  rw [intrinsicAuthPathM_eq_ofFnM]
  refine sequenceFin_bridge _ _ _ fun j => ?_
  have hi : i.val < 14 := i.isLt
  rw [sibling_global j.isLt]
  refine simulateQ_forsNode sk pk a hk j.val _ ?_
  have hq : leaf / 2 ^ j.val < 2 ^ (forsHeight - j.val) := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, Nat.sub_add_cancel j.isLt.le]
    exact hleaf
  have hx := xor_one_lt_pow (by have := j.isLt; simp only [forsHeight] at this ⊢; omega) hq
  have hmul : 2 ^ j.val * 2 ^ (forsHeight - j.val) = 2 ^ 12 := by
    rw [← pow_add, Nat.add_sub_cancel' j.isLt.le]; rfl
  generalize Nat.xor (leaf / 2 ^ j.val) 1 = x at hx ⊢
  generalize 2 ^ (forsHeight - j.val) = P at hx hmul ⊢
  generalize 2 ^ j.val = Q at hmul ⊢
  have : Q * (i.val * P + x + 1) ≤ Q * ((i.val + 1) * P) := Nat.mul_le_mul_left _ (by nlinarith)
  nlinarith

/-- **FORS signing**: the paper's `Fors.sign` is FIPS 205's `forsSignWithSecretM` over the
oracle-secret provider, whenever the paper's indices are FIPS 205's `forsIdx` of `md`. Both draw
each tree's selected secret and then its authentication path. -/
theorem simulateQ_forsSign (indices : Fors.Indices) (md : List Byte)
    (hidx : ∀ i : Fin forsTrees, forsIdx FIPS205.params.params md i.val = (indices i).val)
    (sk pk : Digest) (a : Address) (hk : a.kind = .forsTree) :
    𝓡 (Fors.sign indices sk pk a : OracleComp OracleWorld ForsSignature) =
      (fun v i => forsTreeOfCore (v[i.val]'i.isLt)) <$>
        𝓔 (forsSignWithSecretM FIPS205.core
          (oracleSecret FIPS205.core (Equiv.refl _) (digestEquiv pk) (digestEquiv sk)) md
          (digestEquiv pk) (toAdrs a) :
          OracleComp TypedWorld (ForsSigCore FIPS205.params.params FIPS205.core)) := by
  refine sequenceFin_bridge _ _ forsTreeOfCore fun i => ?_
  rw [← hidx i]
  have hl : forsIdx FIPS205.params.params md i.val < 2 ^ forsHeight := forsIdx_lt _ _ _
  have hi : i.val < 14 := i.isLt
  have hidx32 : i.val * 2 ^ forsHeight + forsIdx FIPS205.params.params md i.val < 2 ^ 32 := by
    simp only [forsHeight] at hl ⊢
    omega
  refine bind_bridge (simulateQ_forsSecret sk pk a hidx32) fun y => ?_
  exact bind_bridge (simulateQ_forsAuthPath sk pk a hk i hl) fun path =>
    pure_bridge _ _ _ rfl

/-! ## FORS public keys from signatures -/

/-- **FORS public keys from signatures**: the paper's recovery from the paper reading of a FIPS 205
FORS signature is `forsPkFromSigM`: per tree the leaf hash and the climb, then `T_k` of the roots
at the FORS-roots address, whenever the paper's indices are FIPS 205's `forsIdx` of `md`. -/
theorem simulateQ_forsPublicKeyFromSignature
    (sig : ForsSigCore FIPS205.params.params FIPS205.core) (indices : Fors.Indices)
    (md : List Byte)
    (hidx : ∀ i : Fin forsTrees, forsIdx FIPS205.params.params md i.val = (indices i).val)
    (pk : Digest) (a : Address) (hk : a.kind = .forsTree) :
    𝓡 (Fors.publicKeyFromSignature (fun i => forsTreeOfCore (sig[i.val]'i.isLt)) indices pk a :
        OracleComp OracleWorld Digest) =
      digestEquiv.symm <$>
        𝓔 (forsPkFromSigM FIPS205.core sig md (digestEquiv pk) (toAdrs a) :
          OracleComp TypedWorld FIPS205.core.Y) := by
  refine bind_bridge (sequenceFin_bridge _ _ digestEquiv.symm fun i => ?_) fun roots => ?_
  · rw [← hidx i]
    have hl : forsIdx FIPS205.params.params md i.val < 2 ^ forsHeight := forsIdx_lt _ _ _
    have hi : i.val < 14 := i.isLt
    have hidx32 : i.val * 2 ^ forsHeight + forsIdx FIPS205.params.params md i.val < 2 ^ 32 := by
      simp only [forsHeight] at hl ⊢
      omega
    have hleaf := simulateQ_tweakable_f pk
      (Fors.nodeAddress a 0 (i.val * 2 ^ forsHeight + forsIdx FIPS205.params.params md i.val))
      (toBytes_forsNodeAdrs a hk (by norm_num) hidx32) (digestEquiv.symm (sig[i.val]'i.isLt).sk)
    rw [Equiv.apply_symm_apply] at hleaf
    refine bind_bridge hleaf fun y => ?_
    rw [climbM_toList]
    refine foldlM_bridge _ _ _ (fun y j => ?_) y
    have hj : j.val < forsHeight := j.isLt
    have hpar := global_div_pow_mod_two (i := i.val)
      (leaf := forsIdx FIPS205.params.params md i.val) hj
    have hz : j.val + 1 < 2 ^ 32 := by simp only [forsHeight] at hj; omega
    have hidx' : (i.val * 2 ^ forsHeight + forsIdx FIPS205.params.params md i.val) /
        2 ^ (j.val + 1) < 2 ^ 32 := lt_of_le_of_lt (Nat.div_le_self _ _) hidx32
    have hnode := simulateQ_tweakable_h pk (Fors.nodeAddress a (j.val + 1)
      ((i.val * 2 ^ forsHeight + forsIdx FIPS205.params.params md i.val) / 2 ^ (j.val + 1)))
      (toBytes_forsNodeAdrs a hk hz hidx')
    have hl := hnode (digestEquiv.symm y)
      (digestEquiv.symm ((sig[i.val]'i.isLt).auth[j.val]'j.isLt))
    have hr := hnode (digestEquiv.symm ((sig[i.val]'i.isLt).auth[j.val]'j.isLt))
      (digestEquiv.symm y)
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at hl hr
    by_cases hc : forsIdx FIPS205.params.params md i.val / 2 ^ j.val % 2 = 0
    · simp only [hc, ite_true]
      split_ifs with h'
      · exact hl
      · exact absurd (hpar.trans hc) h'
    · simp only [hc, ite_false]
      split_ifs with h'
      · exact absurd (hpar.symm.trans h') hc
      · exact hr
  · have hA : (forsPkAdrs (toAdrs a)).toBytes =
        ({ a.setTypeAndClear .forsRoots with keyPair := a.keyPair } : Address).toBytes := by
      rw [← toAdrs_forsRootsAddress, toBytes_toAdrs]
    simp only []
    rw [digestArrayBytes_eq, simulateQ_tweakable_tl pk _ hA]
    congr 3
    apply List.ext_getElem
    · simp only [List.length_map, List.length_ofFn, Vector.length_toList]
      rfl
    · intro i _ _
      simp only [List.getElem_map, List.getElem_ofFn, Equiv.apply_symm_apply,
        Vector.getElem_toList]
      rfl

/-! ## At the digest split of an `H_msg` answer -/

/-- The FORS address of a digest is a FORS-tree address. -/
theorem kind_forsAddress (h : HashOutput) : (Scheme.forsAddress h).kind = .forsTree := rfl

/-- `simulateQ_forsSign` at the digest split of an `H_msg` answer `h`. -/
theorem simulateQ_forsSign_parts (h : HashOutput) (sk pk : Digest) :
    𝓡 (Fors.sign (MessageDigest.forsIndices h) sk pk (Scheme.forsAddress h) :
        OracleComp OracleWorld ForsSignature) =
      (fun v i => forsTreeOfCore (v[i.val]'i.isLt)) <$>
        𝓔 (forsSignWithSecretM FIPS205.core
          (oracleSecret FIPS205.core (Equiv.refl _) (digestEquiv pk) (digestEquiv sk))
          (parts h).md.toList (digestEquiv pk) (parts h).forsAdrs :
          OracleComp TypedWorld (ForsSigCore FIPS205.params.params FIPS205.core)) := by
  rw [← toAdrs_forsAddress]
  exact simulateQ_forsSign _ _ (forsIdx_parts h) sk pk _ (kind_forsAddress h)

/-- `simulateQ_forsPublicKeyFromSignature` at the digest split of an `H_msg` answer `h`. -/
theorem simulateQ_forsPublicKeyFromSignature_parts (h : HashOutput)
    (sig : ForsSigCore FIPS205.params.params FIPS205.core) (pk : Digest) :
    𝓡 (Fors.publicKeyFromSignature (fun i => forsTreeOfCore (sig[i.val]'i.isLt))
        (MessageDigest.forsIndices h) pk (Scheme.forsAddress h) :
        OracleComp OracleWorld Digest) =
      digestEquiv.symm <$>
        𝓔 (forsPkFromSigM FIPS205.core sig (parts h).md.toList (digestEquiv pk)
          (parts h).forsAdrs : OracleComp TypedWorld FIPS205.core.Y) := by
  rw [← toAdrs_forsAddress]
  exact simulateQ_forsPublicKeyFromSignature sig _ _ (forsIdx_parts h) pk _ (kind_forsAddress h)

end SLHDSA.SHAKE128s.Bridge
