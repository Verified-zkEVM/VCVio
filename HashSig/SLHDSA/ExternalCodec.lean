/-
Copyright (c) 2026 Nicolas Consigny. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Consigny
-/

module
public import HashSig.SLHDSA.Concrete.FIPS
public import HashSig.SLHDSA.GeneralScheme
public import HashSig.SLHDSA.Codec

/-!
# Semantic external byte codecs for SLH-DSA

This module refines the exact-width raw codecs into the FIPS 205 component layouts for public
keys, secret keys, and arbitrary-depth internal signatures. The signature wire order is
\`R || SIG_FORS || SIG_HT\`: each FORS row is secret value then authentication path, and each
XMSS row is WOTS+ signature then authentication path. All layouts are intrinsic vectors; decoding
rejects every non-exact length before constructing a semantic value.

This is a codec boundary only. Context encoding, prehash selection, randomized signing, and
external keygen/sign/verify wrappers belong to the subsequent API layer.

## References

- NIST FIPS 205, Sections 4.2 and 9, Algorithms 18--20
-/

@[expose] public section

namespace SLHDSA.ExternalCodec

def unflatten {α : Type} (m n : ℕ) (xs : Vector α (m * n)) :
    Vector (Vector α n) m :=
  Vector.ofFn fun i => Vector.ofFn fun j =>
    xs[i.val * n + j.val]'(by
      calc
        i.val * n + j.val < i.val * n + n := Nat.add_lt_add_left j.isLt _
        _ = (i.val + 1) * n := (Nat.succ_mul i.val n).symm
        _ ≤ m * n := Nat.mul_le_mul_right n (Nat.succ_le_of_lt i.isLt))

@[simp] theorem unflatten_flatten {α : Type} {m n : ℕ}
    (xs : Vector (Vector α n) m) : unflatten m n xs.flatten = xs := by
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  simp only [unflatten, Vector.getElem_ofFn, Vector.getElem_flatten]
  have hn : 0 < n := by omega
  have hdiv : (i * n + j) / n = i := by
    calc
      (i * n + j) / n = (n * i + j) / n := by rw [Nat.mul_comm i n]
      _ = i + j / n := Nat.mul_add_div hn i j
      _ = i := by rw [Nat.div_eq_of_lt hj]; omega
  have hmod : (i * n + j) % n = j := by
    rw [Nat.mul_comm i n, Nat.mul_add_mod]
    exact Nat.mod_eq_of_lt (by omega)
  simp only [hdiv, hmod]

@[simp] theorem flatten_unflatten {α : Type} (m n : ℕ)
    (xs : Vector α (m * n)) : (unflatten m n xs).flatten = xs := by
  ext i
  simp only [unflatten, Vector.getElem_flatten, Vector.getElem_ofFn]
  have hidx : i / n * n + i % n = i := Nat.div_add_mod' i n
  simp only [hidx]

theorem cast_cast_cancel {α : Type} {n m : ℕ} (forward : n = m) (backward : m = n)
    (xs : Vector α n) : (xs.cast forward).cast backward = xs := by
  subst m
  rfl

def takeExact {α : Type} {n m : ℕ} (xs : Vector α (n + m)) : Vector α n :=
  Vector.ofFn fun i => xs[i.val]

def dropExact {α : Type} {n m : ℕ} (xs : Vector α (n + m)) : Vector α m :=
  Vector.ofFn fun i => xs[n + i.val]

@[simp] theorem takeExact_append {α : Type} {n m : ℕ}
    (xs : Vector α n) (ys : Vector α m) : takeExact (xs ++ ys) = xs := by
  ext i
  simp [takeExact]

@[simp] theorem dropExact_append {α : Type} {n m : ℕ}
    (xs : Vector α n) (ys : Vector α m) : dropExact (xs ++ ys) = ys := by
  ext i
  simp [dropExact]

@[simp] theorem takeExact_append_dropExact {α : Type} {n m : ℕ}
    (xs : Vector α (n + m)) : takeExact xs ++ dropExact xs = xs := by
  ext i
  by_cases h : i < n
  · simp [takeExact, dropExact, h]
  · have hm : i - n < m := by omega
    rw [Vector.getElem_append_right (by omega) (by omega)]
    simp [dropExact, Nat.add_sub_of_le (by omega : n ≤ i)]

def nodeBlocksEncode {n count : ℕ} (blocks : Vector (Bytes n) count) : List Byte :=
  blocks.flatten.toList

def nodeBlocksDecode (n count : ℕ) (raw : List Byte) :
    Except CodecError (Vector (Bytes n) count) := do
  let bytes ← decodeExact (count * n) raw
  return unflatten count n bytes

@[simp] theorem nodeBlocksDecode_encode {n count : ℕ}
    (blocks : Vector (Bytes n) count) :
    nodeBlocksDecode n count (nodeBlocksEncode blocks) = .ok blocks := by
  rw [show nodeBlocksEncode blocks = encodeExact blocks.flatten by rfl]
  simp [nodeBlocksDecode]

/-- An exact-width decoder that succeeds preserves the complete input, including its length. -/
theorem encodeExact_of_decodeExact_eq_ok {n : ℕ} {raw : List Byte} {bytes : Bytes n}
    (h : decodeExact n raw = .ok bytes) : encodeExact bytes = raw := by
  unfold decodeExact at h
  split at h
  · simp only [Except.ok.injEq] at h
    subst bytes
    simp [encodeExact]
  · simp at h

def signatureNodeCount (p : Params) : ℕ :=
  1 + (p.k * (1 + p.a) + p.d * (p.len + p.hp))

def forsSecretOffset (vp : ValidatedParams) (tree : Fin vp.params.k) :
    Fin (signatureNodeCount vp.params) :=
  ⟨1 + tree.val * (1 + vp.params.a), by
    simp only [signatureNodeCount]
    have hmul := Nat.mul_lt_mul_of_pos_right tree.isLt (by omega : 0 < 1 + vp.params.a)
    omega⟩

def forsAuthOffset (vp : ValidatedParams) (tree : Fin vp.params.k)
    (height : Fin vp.params.a) : Fin (signatureNodeCount vp.params) :=
  ⟨1 + tree.val * (1 + vp.params.a) + 1 + height.val, by
    simp only [signatureNodeCount]
    have hlocal : 1 + height.val < 1 + vp.params.a := by omega
    have hnext : (tree.val + 1) * (1 + vp.params.a) ≤
        vp.params.k * (1 + vp.params.a) :=
      Nat.mul_le_mul_right _ (Nat.succ_le_of_lt tree.isLt)
    have hspan : tree.val * (1 + vp.params.a) + 1 + height.val <
        vp.params.k * (1 + vp.params.a) := by
      calc
        _ < tree.val * (1 + vp.params.a) + (1 + vp.params.a) := by omega
        _ = (tree.val + 1) * (1 + vp.params.a) := by ring
        _ ≤ _ := hnext
    omega⟩

def xmssWotsOffset (vp : ValidatedParams) (layer : Fin vp.params.d)
    (chain : Fin vp.params.len) : Fin (signatureNodeCount vp.params) :=
  ⟨1 + vp.params.k * (1 + vp.params.a) +
      layer.val * (vp.params.len + vp.params.hp) + chain.val, by
    simp only [signatureNodeCount]
    have hlocal : chain.val < vp.params.len + vp.params.hp :=
      lt_of_lt_of_le chain.isLt (Nat.le_add_right _ _)
    have hnext : (layer.val + 1) * (vp.params.len + vp.params.hp) ≤
        vp.params.d * (vp.params.len + vp.params.hp) :=
      Nat.mul_le_mul_right _ (Nat.succ_le_of_lt layer.isLt)
    have hspan : layer.val * (vp.params.len + vp.params.hp) + chain.val <
        vp.params.d * (vp.params.len + vp.params.hp) := by
      calc
        _ < layer.val * (vp.params.len + vp.params.hp) +
            (vp.params.len + vp.params.hp) := by omega
        _ = (layer.val + 1) * (vp.params.len + vp.params.hp) := by ring
        _ ≤ _ := hnext
    omega⟩

def xmssAuthOffset (vp : ValidatedParams) (layer : Fin vp.params.d)
    (height : Fin vp.params.hp) : Fin (signatureNodeCount vp.params) :=
  ⟨1 + vp.params.k * (1 + vp.params.a) +
      layer.val * (vp.params.len + vp.params.hp) + vp.params.len + height.val, by
    simp only [signatureNodeCount]
    have hlocal : vp.params.len + height.val < vp.params.len + vp.params.hp := by omega
    have hnext : (layer.val + 1) * (vp.params.len + vp.params.hp) ≤
        vp.params.d * (vp.params.len + vp.params.hp) :=
      Nat.mul_le_mul_right _ (Nat.succ_le_of_lt layer.isLt)
    have hspan : layer.val * (vp.params.len + vp.params.hp) +
        vp.params.len + height.val <
        vp.params.d * (vp.params.len + vp.params.hp) := by
      calc
        _ < layer.val * (vp.params.len + vp.params.hp) +
            (vp.params.len + vp.params.hp) := by omega
        _ = (layer.val + 1) * (vp.params.len + vp.params.hp) := by ring
        _ ≤ _ := hnext
    omega⟩

theorem signatureNodeBytes (vp : ValidatedParams) :
    signatureNodeCount vp.params * vp.params.n = vp.params.signatureBytes := by
  rw [signatureNodeCount, Params.signatureBytes, vp.valid.h_eq_layers]
  ring

theorem fipsSignatureNodeBytes (set : FipsParameterSet) :
    signatureNodeCount set.params * set.params.n = set.params.signatureBytes := by
  simpa [FipsParameterSet.validatedParams] using signatureNodeBytes set.validatedParams

def forsTreeOfRow {p : Params} {core : CorePrimitives p}
    (row : Vector core.Y (1 + p.a)) : ForsTreeSigCore p core :=
  { sk := (takeExact row).head, auth := dropExact row }

def rowOfForsTree {p : Params} {core : CorePrimitives p}
    (tree : ForsTreeSigCore p core) : Vector core.Y (1 + p.a) :=
  #v[tree.sk] ++ tree.auth

@[simp] theorem singleton_head_value {α : Type} (x : α) : (#v[x] : Vector α 1).head = x := by
  rfl

@[simp] theorem forsTreeOfRow_rowOfForsTree {p : Params} {core : CorePrimitives p}
    (tree : ForsTreeSigCore p core) : forsTreeOfRow (rowOfForsTree tree) = tree := by
  cases tree
  simp [forsTreeOfRow, rowOfForsTree]

@[simp] theorem rowOfForsTree_forsTreeOfRow {p : Params} {core : CorePrimitives p}
    (row : Vector core.Y (1 + p.a)) : rowOfForsTree (forsTreeOfRow row) = row := by
  change #v[(takeExact row).head] ++ dropExact row = row
  have hsingle : #v[(takeExact row).head] = takeExact row := by
    apply Vector.ext
    intro i hi
    have hzero : i = 0 := by omega
    subst i
    rfl
  rw [hsingle]
  exact takeExact_append_dropExact row

def xmssOfRow {p : Params} {core : CorePrimitives p}
    (row : Vector core.Y (p.len + p.hp)) : XmssSig p core :=
  { wots := takeExact row, auth := dropExact row }

def rowOfXmss {p : Params} {core : CorePrimitives p}
    (sig : XmssSig p core) : Vector core.Y (p.len + p.hp) :=
  sig.wots ++ sig.auth

@[simp] theorem xmssOfRow_rowOfXmss {p : Params} {core : CorePrimitives p}
    (sig : XmssSig p core) : xmssOfRow (rowOfXmss sig) = sig := by
  cases sig
  simp [xmssOfRow, rowOfXmss]

@[simp] theorem rowOfXmss_xmssOfRow {p : Params} {core : CorePrimitives p}
    (row : Vector core.Y (p.len + p.hp)) : rowOfXmss (xmssOfRow row) = row := by
  exact takeExact_append_dropExact row

@[simp] theorem singleton_head {α : Type} (xs : Vector α 1) : #v[xs.head] = xs := by
  apply Vector.ext
  intro i hi
  have hzero : i = 0 := by omega
  subst i
  rfl

def coreSignatureOfNodes (vp : ValidatedParams) (core : CorePrimitives vp.params)
    (nodes : Vector core.Y (signatureNodeCount vp.params)) :
    GeneralScheme.SignatureCore vp core :=
  let rest : Vector core.Y
      (vp.params.k * (1 + vp.params.a) + vp.params.d * (vp.params.len + vp.params.hp)) :=
    dropExact nodes
  let forsFlat : Vector core.Y (vp.params.k * (1 + vp.params.a)) := takeExact rest
  let htFlat : Vector core.Y (vp.params.d * (vp.params.len + vp.params.hp)) := dropExact rest
  { randomness := (takeExact nodes).head
    fors := (unflatten vp.params.k (1 + vp.params.a) forsFlat).map forsTreeOfRow
    hypertree := (unflatten vp.params.d (vp.params.len + vp.params.hp) htFlat).map xmssOfRow }

def nodesOfCoreSignature (vp : ValidatedParams) (core : CorePrimitives vp.params)
    (sig : GeneralScheme.SignatureCore vp core) :
    Vector core.Y (signatureNodeCount vp.params) :=
  #v[sig.randomness] ++
    ((sig.fors.map rowOfForsTree).flatten ++
      (sig.hypertree.map rowOfXmss).flatten)

@[simp] theorem coreSignatureOfNodes_nodesOfCoreSignature
    (vp : ValidatedParams) (core : CorePrimitives vp.params)
    (sig : GeneralScheme.SignatureCore vp core) :
    coreSignatureOfNodes vp core (nodesOfCoreSignature vp core sig) = sig := by
  cases sig
  simp [coreSignatureOfNodes, nodesOfCoreSignature, Function.comp_def]

@[simp] theorem nodesOfCoreSignature_coreSignatureOfNodes
    (vp : ValidatedParams) (core : CorePrimitives vp.params)
    (nodes : Vector core.Y (signatureNodeCount vp.params)) :
    nodesOfCoreSignature vp core (coreSignatureOfNodes vp core nodes) = nodes := by
  simp [coreSignatureOfNodes, nodesOfCoreSignature, Function.comp_def]
  simpa [signatureNodeCount] using takeExact_append_dropExact nodes

def coreSignatureNodeEquiv (vp : ValidatedParams) (core : CorePrimitives vp.params)
    {Z : Type} (e : core.Y ≃ Z) :
    GeneralScheme.SignatureCore vp core ≃ Vector Z (signatureNodeCount vp.params) where
  toFun signature := (nodesOfCoreSignature vp core signature).map e
  invFun nodes := coreSignatureOfNodes vp core (nodes.map e.symm)
  left_inv signature := by
    change coreSignatureOfNodes vp core
      (((nodesOfCoreSignature vp core signature).map e).map e.symm) = signature
    have h : ((nodesOfCoreSignature vp core signature).map e).map e.symm =
        nodesOfCoreSignature vp core signature := by
      ext i
      simp
    rw [h, coreSignatureOfNodes_nodesOfCoreSignature]
  right_inv nodes := by
    change (nodesOfCoreSignature vp core
      (coreSignatureOfNodes vp core (nodes.map e.symm))).map e = nodes
    rw [nodesOfCoreSignature_coreSignatureOfNodes]
    ext i
    simp

@[simp] theorem coreSignatureNodeEquiv_randomness_block?
    (vp : ValidatedParams) (core : CorePrimitives vp.params) {Z : Type} (e : core.Y ≃ Z)
    (signature : GeneralScheme.SignatureCore vp core) :
    (coreSignatureNodeEquiv vp core e signature)[0]? = some (e signature.randomness) := by
  change (Vector.map e (nodesOfCoreSignature vp core signature))[0]? = _
  rw [Vector.getElem?_map]
  have h : (nodesOfCoreSignature vp core signature)[0]? = some signature.randomness := by
    unfold nodesOfCoreSignature signatureNodeCount
    rw [Vector.getElem?_append_left (by omega)]
    rfl
  rw [h]
  rfl

@[simp] theorem coreSignatureNodeEquiv_fors_secret_block?
    (vp : ValidatedParams) (core : CorePrimitives vp.params) {Z : Type} (e : core.Y ≃ Z)
    (signature : GeneralScheme.SignatureCore vp core) (tree : Fin vp.params.k) :
    (coreSignatureNodeEquiv vp core e signature)[(forsSecretOffset vp tree).val]? =
      some (e signature.fors[tree.val].sk) := by
  have hrow : 0 < 1 + vp.params.a := by omega
  have hfors : tree.val * (1 + vp.params.a) < vp.params.k * (1 + vp.params.a) :=
    Nat.mul_lt_mul_of_pos_right tree.isLt hrow
  have hnode :
      (nodesOfCoreSignature vp core signature)[(forsSecretOffset vp tree).val]? =
        some signature.fors[tree.val].sk := by
    unfold nodesOfCoreSignature signatureNodeCount forsSecretOffset
    rw [Vector.getElem?_append_right (by omega : 1 ≤ 1 + tree.val * (1 + vp.params.a))]
    simp only [Nat.add_sub_cancel_left]
    rw [Vector.getElem?_append_left hfors]
    rw [Vector.getElem?_flatten]
    simp only [hfors]
    have hdiv : tree.val * (1 + vp.params.a) / (1 + vp.params.a) = tree.val := by
      rw [Nat.mul_comm]
      exact Nat.mul_div_right tree.val hrow
    have hmod : tree.val * (1 + vp.params.a) % (1 + vp.params.a) = 0 := by
      rw [Nat.mul_comm]
      exact Nat.mul_mod_right _ _
    simp [hdiv, hmod, rowOfForsTree]
  change (Vector.map e (nodesOfCoreSignature vp core signature))[
    (forsSecretOffset vp tree).val]? = _
  rw [Vector.getElem?_map, hnode]
  rfl

@[simp] theorem coreSignatureNodeEquiv_fors_auth_block?
    (vp : ValidatedParams) (core : CorePrimitives vp.params) {Z : Type} (e : core.Y ≃ Z)
    (signature : GeneralScheme.SignatureCore vp core) (tree : Fin vp.params.k)
    (height : Fin vp.params.a) :
    (coreSignatureNodeEquiv vp core e signature)[(forsAuthOffset vp tree height).val]? =
      some (e signature.fors[tree.val].auth[height.val]) := by
  have hrow : 0 < 1 + vp.params.a := by omega
  have hlocal : 1 + height.val < 1 + vp.params.a := by omega
  have hfors : tree.val * (1 + vp.params.a) + 1 + height.val <
      vp.params.k * (1 + vp.params.a) := by
    calc
      _ < (tree.val + 1) * (1 + vp.params.a) := by
        rw [Nat.add_mul]
        omega
      _ ≤ vp.params.k * (1 + vp.params.a) :=
        Nat.mul_le_mul_right _ (Nat.succ_le_of_lt tree.isLt)
  have hdiv :
      (tree.val * (1 + vp.params.a) + 1 + height.val) / (1 + vp.params.a) = tree.val := by
    calc
      _ = ((1 + vp.params.a) * tree.val + (1 + height.val)) /
          (1 + vp.params.a) := by congr 1; ring
      _ = tree.val + (1 + height.val) / (1 + vp.params.a) :=
        Nat.mul_add_div hrow tree.val (1 + height.val)
      _ = tree.val := by rw [Nat.div_eq_of_lt hlocal]; omega
  have hmod :
      (tree.val * (1 + vp.params.a) + 1 + height.val) % (1 + vp.params.a) =
        1 + height.val := by
    rw [show tree.val * (1 + vp.params.a) + 1 + height.val =
      (1 + vp.params.a) * tree.val + (1 + height.val) by ring, Nat.mul_add_mod]
    exact Nat.mod_eq_of_lt hlocal
  have hnode :
      (nodesOfCoreSignature vp core signature)[(forsAuthOffset vp tree height).val]? =
        some signature.fors[tree.val].auth[height.val] := by
    unfold nodesOfCoreSignature signatureNodeCount forsAuthOffset
    let rest := (signature.fors.map rowOfForsTree).flatten ++
      (signature.hypertree.map rowOfXmss).flatten
    change (#v[signature.randomness] ++ rest)[
      1 + tree.val * (1 + vp.params.a) + 1 + height.val]? = _
    rw [Vector.getElem?_append_right (xs := #v[signature.randomness]) (by omega)]
    rw [show 1 + tree.val * (1 + vp.params.a) + 1 + height.val - 1 =
      tree.val * (1 + vp.params.a) + 1 + height.val by omega]
    rw [Vector.getElem?_append_left hfors]
    rw [Vector.getElem?_flatten]
    simp only [hfors]
    simp [hdiv, hmod, rowOfForsTree]
  change (Vector.map e (nodesOfCoreSignature vp core signature))[
    (forsAuthOffset vp tree height).val]? = _
  rw [Vector.getElem?_map, hnode]
  rfl

@[simp] theorem coreSignatureNodeEquiv_xmss_wots_block?
    (vp : ValidatedParams) (core : CorePrimitives vp.params) {Z : Type} (e : core.Y ≃ Z)
    (signature : GeneralScheme.SignatureCore vp core) (layer : Fin vp.params.d)
    (chain : Fin vp.params.len) :
    (coreSignatureNodeEquiv vp core e signature)[(xmssWotsOffset vp layer chain).val]? =
      some (e signature.hypertree[layer.val].wots[chain.val]) := by
  have hrow : 0 < vp.params.len + vp.params.hp := by
    have := vp.valid.hp_pos
    omega
  have hlocal : chain.val < vp.params.len + vp.params.hp := by omega
  have hht : layer.val * (vp.params.len + vp.params.hp) + chain.val <
      vp.params.d * (vp.params.len + vp.params.hp) := by
    calc
      _ < (layer.val + 1) * (vp.params.len + vp.params.hp) := by
        rw [Nat.add_mul]
        omega
      _ ≤ vp.params.d * (vp.params.len + vp.params.hp) :=
        Nat.mul_le_mul_right _ (Nat.succ_le_of_lt layer.isLt)
  have hdiv :
      (layer.val * (vp.params.len + vp.params.hp) + chain.val) /
          (vp.params.len + vp.params.hp) = layer.val := by
    calc
      _ = ((vp.params.len + vp.params.hp) * layer.val + chain.val) /
          (vp.params.len + vp.params.hp) := by congr 1; ring
      _ = layer.val + chain.val / (vp.params.len + vp.params.hp) :=
        Nat.mul_add_div hrow layer.val chain.val
      _ = layer.val := by rw [Nat.div_eq_of_lt hlocal]; omega
  have hmod :
      (layer.val * (vp.params.len + vp.params.hp) + chain.val) %
          (vp.params.len + vp.params.hp) = chain.val := by
    rw [show layer.val * (vp.params.len + vp.params.hp) + chain.val =
      (vp.params.len + vp.params.hp) * layer.val + chain.val by ring, Nat.mul_add_mod]
    exact Nat.mod_eq_of_lt hlocal
  have hnode :
      (nodesOfCoreSignature vp core signature)[(xmssWotsOffset vp layer chain).val]? =
        some signature.hypertree[layer.val].wots[chain.val] := by
    unfold nodesOfCoreSignature signatureNodeCount xmssWotsOffset
    let forsFlat := (signature.fors.map rowOfForsTree).flatten
    let htFlat := (signature.hypertree.map rowOfXmss).flatten
    change (#v[signature.randomness] ++ (forsFlat ++ htFlat))[
      1 + vp.params.k * (1 + vp.params.a) +
        layer.val * (vp.params.len + vp.params.hp) + chain.val]? = _
    rw [Vector.getElem?_append_right (xs := #v[signature.randomness]) (by omega)]
    rw [show 1 + vp.params.k * (1 + vp.params.a) +
        layer.val * (vp.params.len + vp.params.hp) + chain.val - 1 =
      vp.params.k * (1 + vp.params.a) +
        (layer.val * (vp.params.len + vp.params.hp) + chain.val) by omega]
    rw [Vector.getElem?_append_right (xs := forsFlat) (by omega)]
    rw [show vp.params.k * (1 + vp.params.a) +
        (layer.val * (vp.params.len + vp.params.hp) + chain.val) -
        vp.params.k * (1 + vp.params.a) =
      layer.val * (vp.params.len + vp.params.hp) + chain.val by omega]
    rw [Vector.getElem?_flatten]
    simp only [hht]
    simp [hdiv, hmod, rowOfXmss]
  change (Vector.map e (nodesOfCoreSignature vp core signature))[
    (xmssWotsOffset vp layer chain).val]? = _
  rw [Vector.getElem?_map, hnode]
  rfl

@[simp] theorem coreSignatureNodeEquiv_xmss_auth_block?
    (vp : ValidatedParams) (core : CorePrimitives vp.params) {Z : Type} (e : core.Y ≃ Z)
    (signature : GeneralScheme.SignatureCore vp core) (layer : Fin vp.params.d)
    (height : Fin vp.params.hp) :
    (coreSignatureNodeEquiv vp core e signature)[(xmssAuthOffset vp layer height).val]? =
      some (e signature.hypertree[layer.val].auth[height.val]) := by
  have hrow : 0 < vp.params.len + vp.params.hp := by
    have := vp.valid.hp_pos
    omega
  have hlocal : vp.params.len + height.val < vp.params.len + vp.params.hp := by omega
  have hht : layer.val * (vp.params.len + vp.params.hp) + vp.params.len + height.val <
      vp.params.d * (vp.params.len + vp.params.hp) := by
    calc
      _ < (layer.val + 1) * (vp.params.len + vp.params.hp) := by
        rw [Nat.add_mul]
        omega
      _ ≤ vp.params.d * (vp.params.len + vp.params.hp) :=
        Nat.mul_le_mul_right _ (Nat.succ_le_of_lt layer.isLt)
  have hdiv :
      (layer.val * (vp.params.len + vp.params.hp) + vp.params.len + height.val) /
          (vp.params.len + vp.params.hp) = layer.val := by
    calc
      _ = ((vp.params.len + vp.params.hp) * layer.val +
          (vp.params.len + height.val)) / (vp.params.len + vp.params.hp) := by
        congr 1
        ring
      _ = layer.val + (vp.params.len + height.val) /
          (vp.params.len + vp.params.hp) :=
        Nat.mul_add_div hrow layer.val (vp.params.len + height.val)
      _ = layer.val := by rw [Nat.div_eq_of_lt hlocal]; omega
  have hmod :
      (layer.val * (vp.params.len + vp.params.hp) + vp.params.len + height.val) %
          (vp.params.len + vp.params.hp) = vp.params.len + height.val := by
    rw [show layer.val * (vp.params.len + vp.params.hp) + vp.params.len + height.val =
      (vp.params.len + vp.params.hp) * layer.val +
        (vp.params.len + height.val) by ring, Nat.mul_add_mod]
    exact Nat.mod_eq_of_lt hlocal
  have hnode :
      (nodesOfCoreSignature vp core signature)[(xmssAuthOffset vp layer height).val]? =
        some signature.hypertree[layer.val].auth[height.val] := by
    unfold nodesOfCoreSignature signatureNodeCount xmssAuthOffset
    let forsFlat := (signature.fors.map rowOfForsTree).flatten
    let htFlat := (signature.hypertree.map rowOfXmss).flatten
    change (#v[signature.randomness] ++ (forsFlat ++ htFlat))[
      1 + vp.params.k * (1 + vp.params.a) +
        layer.val * (vp.params.len + vp.params.hp) + vp.params.len + height.val]? = _
    rw [Vector.getElem?_append_right (xs := #v[signature.randomness]) (by omega)]
    rw [show 1 + vp.params.k * (1 + vp.params.a) +
        layer.val * (vp.params.len + vp.params.hp) + vp.params.len + height.val - 1 =
      vp.params.k * (1 + vp.params.a) +
        (layer.val * (vp.params.len + vp.params.hp) + vp.params.len + height.val) by omega]
    rw [Vector.getElem?_append_right (xs := forsFlat) (by omega)]
    rw [show vp.params.k * (1 + vp.params.a) +
        (layer.val * (vp.params.len + vp.params.hp) + vp.params.len + height.val) -
        vp.params.k * (1 + vp.params.a) =
      layer.val * (vp.params.len + vp.params.hp) + vp.params.len + height.val by omega]
    rw [Vector.getElem?_flatten]
    simp only [hht]
    simp [hdiv, hmod, rowOfXmss]
  change (Vector.map e (nodesOfCoreSignature vp core signature))[
    (xmssAuthOffset vp layer height).val]? = _
  rw [Vector.getElem?_map, hnode]
  rfl

def signatureBlockByteOffset (vp : ValidatedParams)
    (block : Fin (signatureNodeCount vp.params)) : Nat := block.val * vp.params.n

def randomnessByteOffset (_vp : ValidatedParams) : Nat := 0

def forsSecretByteOffset (vp : ValidatedParams) (tree : Fin vp.params.k) : Nat :=
  signatureBlockByteOffset vp (forsSecretOffset vp tree)

def forsAuthByteOffset (vp : ValidatedParams) (tree : Fin vp.params.k)
    (height : Fin vp.params.a) : Nat :=
  signatureBlockByteOffset vp (forsAuthOffset vp tree height)

def xmssWotsByteOffset (vp : ValidatedParams) (layer : Fin vp.params.d)
    (chain : Fin vp.params.len) : Nat :=
  signatureBlockByteOffset vp (xmssWotsOffset vp layer chain)

def xmssAuthByteOffset (vp : ValidatedParams) (layer : Fin vp.params.d)
    (height : Fin vp.params.hp) : Nat :=
  signatureBlockByteOffset vp (xmssAuthOffset vp layer height)

structure PublicKey (set : FipsParameterSet) where
  blocks : Vector (Bytes set.params.n) 2
deriving Repr, DecidableEq

structure SecretKey (set : FipsParameterSet) where
  blocks : Vector (Bytes set.params.n) 4
deriving Repr, DecidableEq

structure Signature (set : FipsParameterSet) where
  blocks : Vector (Bytes set.params.n) (signatureNodeCount set.params)
deriving Repr, DecidableEq

variable {set : FipsParameterSet}

def approvedPkSeedEquiv (set : FipsParameterSet) :
    (Concrete.approvedPrimitives set).PkSeed ≃ Bytes set.params.n := by
  cases set <;> exact Equiv.refl _

def approvedSkSeedEquiv (set : FipsParameterSet) :
    (Concrete.approvedPrimitives set).SkSeed ≃ Bytes set.params.n := by
  cases set <;> exact Equiv.refl _

def approvedSkPrfEquiv (set : FipsParameterSet) :
    (Concrete.approvedPrimitives set).SkPrf ≃ Bytes set.params.n := by
  cases set <;> exact Equiv.refl _

def approvedYEquiv (set : FipsParameterSet) :
    (Concrete.approvedPrimitives set).Y ≃ Bytes set.params.n := by
  cases set <;> exact Equiv.refl _

theorem vector2_reconstruct {α : Type} (xs : Vector α 2) : #v[xs[0], xs[1]] = xs := by
  apply Vector.ext
  intro i hi
  interval_cases i <;> rfl

theorem vector4_reconstruct {α : Type} (xs : Vector α 4) :
    #v[xs[0], xs[1], xs[2], xs[3]] = xs := by
  apply Vector.ext
  intro i hi
  interval_cases i <;> rfl

@[simp] theorem map_equiv_map_symm {α β : Type} {n : ℕ} (e : α ≃ β)
    (xs : Vector β n) : (xs.map e.symm).map e = xs := by
  ext i
  simp

@[simp] theorem map_symm_map_equiv {α β : Type} {n : ℕ} (e : α ≃ β)
    (xs : Vector α n) : (xs.map e).map e.symm = xs := by
  ext i
  simp

namespace PublicKey

def toBytes (key : PublicKey set) : PublicKeyBytes set :=
  key.blocks.flatten.cast (by simp [Params.publicKeyBytes])

def ofBytes (bytes : PublicKeyBytes set) : PublicKey set :=
  ⟨unflatten 2 set.params.n
    (bytes.cast (by simp [Params.publicKeyBytes]))⟩

@[simp] theorem ofBytes_toBytes (key : PublicKey set) : ofBytes (toBytes key) = key := by
  rcases key with ⟨blocks⟩
  simp [toBytes, ofBytes]

@[simp] theorem toBytes_ofBytes (bytes : PublicKeyBytes set) : toBytes (ofBytes bytes) = bytes := by
  simp [toBytes, ofBytes]

def encode (key : PublicKey set) : List Byte := SLHDSA.encodePublicKey key.toBytes

def decode (set : FipsParameterSet) (raw : List Byte) : Except CodecError (PublicKey set) :=
  (SLHDSA.decodePublicKey set raw).map ofBytes

@[simp] theorem decode_encode (key : PublicKey set) :
    decode set (encode key) = .ok key := by
  change (SLHDSA.decodePublicKey set (SLHDSA.encodePublicKey key.toBytes)).map ofBytes = _
  rw [SLHDSA.decodePublicKey_encode]
  change Except.ok (ofBytes key.toBytes) = Except.ok key
  rw [ofBytes_toBytes]

theorem encode_of_decode_eq_ok {raw : List Byte} {key : PublicKey set}
    (h : decode set raw = .ok key) : encode key = raw := by
  unfold decode at h
  generalize hdecoded : SLHDSA.decodePublicKey set raw = decoded at h
  cases decoded with
  | error error => cases h
  | ok bytes =>
      simp only [Except.map, Except.ok.injEq] at h
      subst key
      change SLHDSA.encodePublicKey (toBytes (ofBytes bytes)) = raw
      rw [toBytes_ofBytes]
      apply encodeExact_of_decodeExact_eq_ok
      simpa [SLHDSA.decodePublicKey] using hdecoded

def toInternal (key : PublicKey set) :
    PublicKeyCore (Concrete.approvedPrimitives set).core :=
  ⟨(approvedPkSeedEquiv set).symm key.blocks[0],
    (approvedYEquiv set).symm key.blocks[1]⟩

def ofInternal (key : PublicKeyCore (Concrete.approvedPrimitives set).core) :
    PublicKey set :=
  ⟨#v[approvedPkSeedEquiv set key.pkSeed, approvedYEquiv set key.pkRoot]⟩

@[simp] theorem ofInternal_pkSeed_block?
    (key : PublicKeyCore (Concrete.approvedPrimitives set).core) :
    (ofInternal key).blocks[0]? = some (approvedPkSeedEquiv set key.pkSeed) := by
  rfl

@[simp] theorem ofInternal_pkRoot_block?
    (key : PublicKeyCore (Concrete.approvedPrimitives set).core) :
    (ofInternal key).blocks[1]? = some (approvedYEquiv set key.pkRoot) := by
  rfl

@[simp] theorem toInternal_ofInternal
    (key : PublicKeyCore (Concrete.approvedPrimitives set).core) :
    toInternal (ofInternal key) = key := by
  cases key
  simp [toInternal, ofInternal]

@[simp] theorem ofInternal_toInternal (key : PublicKey set) :
    ofInternal (toInternal key) = key := by
  rcases key with ⟨blocks⟩
  simp only [toInternal, ofInternal, Equiv.apply_symm_apply]
  exact congrArg _root_.SLHDSA.ExternalCodec.PublicKey.mk (vector2_reconstruct blocks)

end PublicKey

namespace SecretKey

def toBytes (key : SecretKey set) : SecretKeyBytes set :=
  key.blocks.flatten.cast (by simp [Params.secretKeyBytes])

def ofBytes (bytes : SecretKeyBytes set) : SecretKey set :=
  ⟨unflatten 4 set.params.n
    (bytes.cast (by simp [Params.secretKeyBytes]))⟩

@[simp] theorem ofBytes_toBytes (key : SecretKey set) : ofBytes (toBytes key) = key := by
  rcases key with ⟨blocks⟩
  simp [toBytes, ofBytes]

@[simp] theorem toBytes_ofBytes (bytes : SecretKeyBytes set) : toBytes (ofBytes bytes) = bytes := by
  simp [toBytes, ofBytes]

def encode (key : SecretKey set) : List Byte := SLHDSA.encodeSecretKey key.toBytes

def decode (set : FipsParameterSet) (raw : List Byte) : Except CodecError (SecretKey set) :=
  (SLHDSA.decodeSecretKey set raw).map ofBytes

@[simp] theorem decode_encode (key : SecretKey set) :
    decode set (encode key) = .ok key := by
  change (SLHDSA.decodeSecretKey set (SLHDSA.encodeSecretKey key.toBytes)).map ofBytes = _
  rw [SLHDSA.decodeSecretKey_encode]
  change Except.ok (ofBytes key.toBytes) = Except.ok key
  rw [ofBytes_toBytes]

theorem encode_of_decode_eq_ok {raw : List Byte} {key : SecretKey set}
    (h : decode set raw = .ok key) : encode key = raw := by
  unfold decode at h
  generalize hdecoded : SLHDSA.decodeSecretKey set raw = decoded at h
  cases decoded with
  | error error => cases h
  | ok bytes =>
      simp only [Except.map, Except.ok.injEq] at h
      subst key
      change SLHDSA.encodeSecretKey (toBytes (ofBytes bytes)) = raw
      rw [toBytes_ofBytes]
      apply encodeExact_of_decodeExact_eq_ok
      simpa [SLHDSA.decodeSecretKey] using hdecoded

def toInternal (key : SecretKey set) :
    SecretKeyCore (Concrete.approvedPrimitives set).core :=
  ⟨(approvedSkSeedEquiv set).symm key.blocks[0],
    (approvedSkPrfEquiv set).symm key.blocks[1],
    (approvedPkSeedEquiv set).symm key.blocks[2],
    (approvedYEquiv set).symm key.blocks[3]⟩

def ofInternal (key : SecretKeyCore (Concrete.approvedPrimitives set).core) :
    SecretKey set :=
  ⟨#v[approvedSkSeedEquiv set key.skSeed, approvedSkPrfEquiv set key.skPrf,
    approvedPkSeedEquiv set key.pkSeed, approvedYEquiv set key.pkRoot]⟩

@[simp] theorem ofInternal_skSeed_block?
    (key : SecretKeyCore (Concrete.approvedPrimitives set).core) :
    (ofInternal key).blocks[0]? = some (approvedSkSeedEquiv set key.skSeed) := by
  rfl

@[simp] theorem ofInternal_skPrf_block?
    (key : SecretKeyCore (Concrete.approvedPrimitives set).core) :
    (ofInternal key).blocks[1]? = some (approvedSkPrfEquiv set key.skPrf) := by
  rfl

@[simp] theorem ofInternal_pkSeed_block?
    (key : SecretKeyCore (Concrete.approvedPrimitives set).core) :
    (ofInternal key).blocks[2]? = some (approvedPkSeedEquiv set key.pkSeed) := by
  rfl

@[simp] theorem ofInternal_pkRoot_block?
    (key : SecretKeyCore (Concrete.approvedPrimitives set).core) :
    (ofInternal key).blocks[3]? = some (approvedYEquiv set key.pkRoot) := by
  rfl

@[simp] theorem toInternal_ofInternal
    (key : SecretKeyCore (Concrete.approvedPrimitives set).core) :
    toInternal (ofInternal key) = key := by
  cases key
  simp [toInternal, ofInternal]

@[simp] theorem ofInternal_toInternal (key : SecretKey set) :
    ofInternal (toInternal key) = key := by
  rcases key with ⟨blocks⟩
  simp only [toInternal, ofInternal, Equiv.apply_symm_apply]
  exact congrArg _root_.SLHDSA.ExternalCodec.SecretKey.mk (vector4_reconstruct blocks)

end SecretKey

namespace Signature

def toBytes (signature : Signature set) : SignatureBytes set :=
  signature.blocks.flatten.cast (fipsSignatureNodeBytes set)

def ofBytes (bytes : SignatureBytes set) : Signature set :=
  ⟨unflatten (signatureNodeCount set.params) set.params.n
    (bytes.cast (fipsSignatureNodeBytes set).symm)⟩

@[simp] theorem ofBytes_toBytes (signature : Signature set) :
    ofBytes (toBytes signature) = signature := by
  rcases signature with ⟨blocks⟩
  apply congrArg Signature.mk
  change unflatten (signatureNodeCount set.params) set.params.n
    ((blocks.flatten.cast (fipsSignatureNodeBytes set)).cast
      (fipsSignatureNodeBytes set).symm) = blocks
  rw [cast_cast_cancel]
  exact unflatten_flatten blocks

@[simp] theorem toBytes_ofBytes (bytes : SignatureBytes set) : toBytes (ofBytes bytes) = bytes := by
  unfold toBytes ofBytes
  rw [flatten_unflatten]
  exact cast_cast_cancel _ _ _

def encode (signature : Signature set) : List Byte := SLHDSA.encodeSignature signature.toBytes

/-- The serialized signature is exactly the row-major flattening of its `n`-byte node blocks. -/
theorem encode_eq_blocks_flatten (signature : Signature set) :
    encode signature = signature.blocks.flatten.toList := by
  rfl

/-- Block `i`, byte `j` occurs at the exact wire offset `i * n + j`. -/
@[simp] theorem encode_block_byte? (signature : Signature set)
    (block : Fin (signatureNodeCount set.params)) (byte : Fin set.params.n) :
    (encode signature)[block.val * set.params.n + byte.val]? =
      some signature.blocks[block.val][byte.val] := by
  rw [encode_eq_blocks_flatten]
  rw [List.getElem?_eq_getElem]
  · have hn : 0 < set.params.n := set.validatedParams.valid.n_pos
    have hdiv : (block.val * set.params.n + byte.val) / set.params.n = block.val := by
      calc
        _ = (set.params.n * block.val + byte.val) / set.params.n := by
          congr 1
          ring
        _ = block.val + byte.val / set.params.n :=
          Nat.mul_add_div hn block.val byte.val
        _ = block.val := by rw [Nat.div_eq_of_lt byte.isLt]; omega
    have hmod : (block.val * set.params.n + byte.val) % set.params.n = byte.val := by
      rw [show block.val * set.params.n + byte.val =
        set.params.n * block.val + byte.val by ring, Nat.mul_add_mod]
      exact Nat.mod_eq_of_lt byte.isLt
    have hidx : block.val * set.params.n + byte.val <
        signatureNodeCount set.params * set.params.n := by
      calc
        block.val * set.params.n + byte.val < block.val * set.params.n + set.params.n :=
          Nat.add_lt_add_left byte.isLt _
        _ = (block.val + 1) * set.params.n := by ring
        _ ≤ signatureNodeCount set.params * set.params.n :=
          Nat.mul_le_mul_right _ (Nat.succ_le_of_lt block.isLt)
    have hlist : block.val * set.params.n + byte.val <
        signature.blocks.flatten.toList.length := by simpa using hidx
    congr 1
    calc
      signature.blocks.flatten.toList[block.val * set.params.n + byte.val] =
          signature.blocks.flatten[block.val * set.params.n + byte.val] :=
        Vector.getElem_toList hlist
      _ = signature.blocks[block.val][byte.val] := by
        rw [Vector.getElem_flatten]
        simp only [hdiv, hmod]
  · simp only [Vector.length_toList]
    calc
      block.val * set.params.n + byte.val < block.val * set.params.n + set.params.n :=
        Nat.add_lt_add_left byte.isLt _
      _ = (block.val + 1) * set.params.n := by ring
      _ ≤ signatureNodeCount set.params * set.params.n :=
        Nat.mul_le_mul_right _ (Nat.succ_le_of_lt block.isLt)

def decode (set : FipsParameterSet) (raw : List Byte) : Except CodecError (Signature set) :=
  (SLHDSA.decodeSignature set raw).map ofBytes

@[simp] theorem decode_encode (signature : Signature set) :
    decode set (encode signature) = .ok signature := by
  change (SLHDSA.decodeSignature set (SLHDSA.encodeSignature signature.toBytes)).map ofBytes = _
  rw [SLHDSA.decodeSignature_encode]
  change Except.ok (ofBytes signature.toBytes) = Except.ok signature
  rw [ofBytes_toBytes]

theorem encode_of_decode_eq_ok {raw : List Byte} {signature : Signature set}
    (h : decode set raw = .ok signature) : encode signature = raw := by
  unfold decode at h
  generalize hdecoded : SLHDSA.decodeSignature set raw = decoded at h
  cases decoded with
  | error error => cases h
  | ok bytes =>
      simp only [Except.map, Except.ok.injEq] at h
      subst signature
      change SLHDSA.encodeSignature (toBytes (ofBytes bytes)) = raw
      rw [toBytes_ofBytes]
      apply encodeExact_of_decodeExact_eq_ok
      simpa [SLHDSA.decodeSignature] using hdecoded

def toInternal (signature : Signature set) :
    GeneralScheme.SignatureCore set.validatedParams (Concrete.approvedPrimitives set).core :=
  (coreSignatureNodeEquiv _ _ (approvedYEquiv set)).symm signature.blocks

def ofInternal
    (signature : GeneralScheme.SignatureCore set.validatedParams
      (Concrete.approvedPrimitives set).core) : Signature set :=
  ⟨coreSignatureNodeEquiv _ _ (approvedYEquiv set) signature⟩

@[simp] theorem toInternal_ofInternal
    (signature : GeneralScheme.SignatureCore set.validatedParams
      (Concrete.approvedPrimitives set).core) :
    toInternal (ofInternal signature) = signature := by
  simpa only [toInternal, ofInternal] using
    (coreSignatureNodeEquiv set.validatedParams (Concrete.approvedPrimitives set).core
      (approvedYEquiv set)).symm_apply_apply signature

@[simp] theorem ofInternal_toInternal (signature : Signature set) :
    ofInternal (toInternal signature) = signature := by
  rcases signature with ⟨blocks⟩
  exact congrArg _root_.SLHDSA.ExternalCodec.Signature.mk
    ((coreSignatureNodeEquiv set.validatedParams (Concrete.approvedPrimitives set).core
      (approvedYEquiv set)).apply_symm_apply blocks)

end Signature

/-! ## Direct semantic codecs -/

abbrev ApprovedPublicKey (set : FipsParameterSet) :=
  PublicKeyCore (Concrete.approvedPrimitives set).core

abbrev ApprovedSecretKey (set : FipsParameterSet) :=
  SecretKeyCore (Concrete.approvedPrimitives set).core

abbrev ApprovedSignature (set : FipsParameterSet) :=
  GeneralScheme.SignatureCore set.validatedParams (Concrete.approvedPrimitives set).core

def encodePublicKeyCore (key : ApprovedPublicKey set) : List Byte :=
  PublicKey.encode (PublicKey.ofInternal key)

def decodePublicKeyCore (set : FipsParameterSet) (raw : List Byte) :
    Except CodecError (ApprovedPublicKey set) :=
  (PublicKey.decode set raw).map PublicKey.toInternal

def encodeSecretKeyCore (key : ApprovedSecretKey set) : List Byte :=
  SecretKey.encode (SecretKey.ofInternal key)

def decodeSecretKeyCore (set : FipsParameterSet) (raw : List Byte) :
    Except CodecError (ApprovedSecretKey set) :=
  (SecretKey.decode set raw).map SecretKey.toInternal

def encodeSignatureCore (signature : ApprovedSignature set) : List Byte :=
  Signature.encode (Signature.ofInternal signature)

def decodeSignatureCore (set : FipsParameterSet) (raw : List Byte) :
    Except CodecError (ApprovedSignature set) :=
  (Signature.decode set raw).map Signature.toInternal

@[simp] theorem decodePublicKeyCore_encode (key : ApprovedPublicKey set) :
    decodePublicKeyCore set (encodePublicKeyCore key) = .ok key := by
  change Except.map PublicKey.toInternal
    (PublicKey.decode set (PublicKey.encode (PublicKey.ofInternal key))) = .ok key
  rw [PublicKey.decode_encode]
  change Except.ok (PublicKey.toInternal (PublicKey.ofInternal key)) = .ok key
  rw [PublicKey.toInternal_ofInternal]

@[simp] theorem decodeSecretKeyCore_encode (key : ApprovedSecretKey set) :
    decodeSecretKeyCore set (encodeSecretKeyCore key) = .ok key := by
  change Except.map SecretKey.toInternal
    (SecretKey.decode set (SecretKey.encode (SecretKey.ofInternal key))) = .ok key
  rw [SecretKey.decode_encode]
  change Except.ok (SecretKey.toInternal (SecretKey.ofInternal key)) = .ok key
  rw [SecretKey.toInternal_ofInternal]

@[simp] theorem decodeSignatureCore_encode (signature : ApprovedSignature set) :
    decodeSignatureCore set (encodeSignatureCore signature) = .ok signature := by
  change Except.map Signature.toInternal
    (Signature.decode set (Signature.encode (Signature.ofInternal signature))) = .ok signature
  rw [Signature.decode_encode]
  change Except.ok (Signature.toInternal (Signature.ofInternal signature)) = .ok signature
  rw [Signature.toInternal_ofInternal]

theorem encodePublicKeyCore_of_decode_eq_ok {raw : List Byte} {key : ApprovedPublicKey set}
    (h : decodePublicKeyCore set raw = .ok key) : encodePublicKeyCore key = raw := by
  unfold decodePublicKeyCore at h
  generalize hdecoded : PublicKey.decode set raw = decoded at h
  cases decoded with
  | error error => cases h
  | ok wireKey =>
      simp only [Except.map, Except.ok.injEq] at h
      subst key
      change PublicKey.encode (PublicKey.ofInternal (PublicKey.toInternal wireKey)) = raw
      rw [PublicKey.ofInternal_toInternal]
      exact PublicKey.encode_of_decode_eq_ok hdecoded

theorem encodeSecretKeyCore_of_decode_eq_ok {raw : List Byte} {key : ApprovedSecretKey set}
    (h : decodeSecretKeyCore set raw = .ok key) : encodeSecretKeyCore key = raw := by
  unfold decodeSecretKeyCore at h
  generalize hdecoded : SecretKey.decode set raw = decoded at h
  cases decoded with
  | error error => cases h
  | ok wireKey =>
      simp only [Except.map, Except.ok.injEq] at h
      subst key
      change SecretKey.encode (SecretKey.ofInternal (SecretKey.toInternal wireKey)) = raw
      rw [SecretKey.ofInternal_toInternal]
      exact SecretKey.encode_of_decode_eq_ok hdecoded

theorem encodeSignatureCore_of_decode_eq_ok {raw : List Byte} {signature : ApprovedSignature set}
    (h : decodeSignatureCore set raw = .ok signature) : encodeSignatureCore signature = raw := by
  unfold decodeSignatureCore at h
  generalize hdecoded : Signature.decode set raw = decoded at h
  cases decoded with
  | error error => cases h
  | ok wireSignature =>
      simp only [Except.map, Except.ok.injEq] at h
      subst signature
      change Signature.encode (Signature.ofInternal (Signature.toInternal wireSignature)) = raw
      rw [Signature.ofInternal_toInternal]
      exact Signature.encode_of_decode_eq_ok hdecoded

@[simp] theorem encodePublicKeyCore_length (key : ApprovedPublicKey set) :
    (encodePublicKeyCore key).length = set.params.publicKeyBytes := by
  simp [encodePublicKeyCore, PublicKey.encode, SLHDSA.encodePublicKey, encodeExact]

@[simp] theorem encodeSecretKeyCore_length (key : ApprovedSecretKey set) :
    (encodeSecretKeyCore key).length = set.params.secretKeyBytes := by
  simp [encodeSecretKeyCore, SecretKey.encode, SLHDSA.encodeSecretKey, encodeExact]

@[simp] theorem encodeSignatureCore_length (signature : ApprovedSignature set) :
    (encodeSignatureCore signature).length = set.params.signatureBytes := by
  simp [encodeSignatureCore, Signature.encode, SLHDSA.encodeSignature, encodeExact]

theorem decodePublicKeyCore_of_length_ne (raw : List Byte)
    (h : raw.length ≠ set.params.publicKeyBytes) :
    decodePublicKeyCore set raw =
      .error (.invalidLength set.params.publicKeyBytes raw.length) := by
  simp [decodePublicKeyCore, PublicKey.decode, SLHDSA.decodePublicKey, decodeExact, h]
  rfl

theorem decodeSecretKeyCore_of_length_ne (raw : List Byte)
    (h : raw.length ≠ set.params.secretKeyBytes) :
    decodeSecretKeyCore set raw =
      .error (.invalidLength set.params.secretKeyBytes raw.length) := by
  simp [decodeSecretKeyCore, SecretKey.decode, SLHDSA.decodeSecretKey, decodeExact, h]
  rfl

theorem decodeSignatureCore_of_length_ne (raw : List Byte)
    (h : raw.length ≠ set.params.signatureBytes) :
    decodeSignatureCore set raw =
      .error (.invalidLength set.params.signatureBytes raw.length) := by
  simp [decodeSignatureCore, Signature.decode, SLHDSA.decodeSignature, decodeExact, h]
  rfl

theorem decodePublicKeyCore_short (raw : List Byte)
    (h : raw.length < set.params.publicKeyBytes) :
    decodePublicKeyCore set raw =
      .error (.invalidLength set.params.publicKeyBytes raw.length) :=
  decodePublicKeyCore_of_length_ne raw (Nat.ne_of_lt h)

theorem decodePublicKeyCore_long (raw : List Byte)
    (h : set.params.publicKeyBytes < raw.length) :
    decodePublicKeyCore set raw =
      .error (.invalidLength set.params.publicKeyBytes raw.length) :=
  decodePublicKeyCore_of_length_ne raw (Nat.ne_of_gt h)

theorem decodeSecretKeyCore_short (raw : List Byte)
    (h : raw.length < set.params.secretKeyBytes) :
    decodeSecretKeyCore set raw =
      .error (.invalidLength set.params.secretKeyBytes raw.length) :=
  decodeSecretKeyCore_of_length_ne raw (Nat.ne_of_lt h)

theorem decodeSecretKeyCore_long (raw : List Byte)
    (h : set.params.secretKeyBytes < raw.length) :
    decodeSecretKeyCore set raw =
      .error (.invalidLength set.params.secretKeyBytes raw.length) :=
  decodeSecretKeyCore_of_length_ne raw (Nat.ne_of_gt h)

theorem decodeSignatureCore_short (raw : List Byte)
    (h : raw.length < set.params.signatureBytes) :
    decodeSignatureCore set raw =
      .error (.invalidLength set.params.signatureBytes raw.length) :=
  decodeSignatureCore_of_length_ne raw (Nat.ne_of_lt h)

theorem decodeSignatureCore_long (raw : List Byte)
    (h : set.params.signatureBytes < raw.length) :
    decodeSignatureCore set raw =
      .error (.invalidLength set.params.signatureBytes raw.length) :=
  decodeSignatureCore_of_length_ne raw (Nat.ne_of_gt h)

theorem decodePublicKeyCore_trailing_byte (raw : List Byte)
    (h : raw.length = set.params.publicKeyBytes) (trailing : Byte) :
    decodePublicKeyCore set (raw ++ [trailing]) =
      .error (.invalidLength set.params.publicKeyBytes (set.params.publicKeyBytes + 1)) := by
  have hne : (raw ++ [trailing]).length ≠ set.params.publicKeyBytes := by simp [h]
  simpa [h] using decodePublicKeyCore_of_length_ne (set := set) (raw ++ [trailing]) hne

theorem decodeSecretKeyCore_trailing_byte (raw : List Byte)
    (h : raw.length = set.params.secretKeyBytes) (trailing : Byte) :
    decodeSecretKeyCore set (raw ++ [trailing]) =
      .error (.invalidLength set.params.secretKeyBytes (set.params.secretKeyBytes + 1)) := by
  have hne : (raw ++ [trailing]).length ≠ set.params.secretKeyBytes := by simp [h]
  simpa [h] using decodeSecretKeyCore_of_length_ne (set := set) (raw ++ [trailing]) hne

theorem decodeSignatureCore_trailing_byte (raw : List Byte)
    (h : raw.length = set.params.signatureBytes) (trailing : Byte) :
    decodeSignatureCore set (raw ++ [trailing]) =
      .error (.invalidLength set.params.signatureBytes (set.params.signatureBytes + 1)) := by
  have hne : (raw ++ [trailing]).length ≠ set.params.signatureBytes := by simp [h]
  simpa [h] using decodeSignatureCore_of_length_ne (set := set) (raw ++ [trailing]) hne

end SLHDSA.ExternalCodec
