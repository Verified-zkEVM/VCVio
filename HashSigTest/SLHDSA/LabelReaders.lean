/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.Security.LabelReaders

/-!
# Honest readers on a merged relabelled state at the FIPS 205 parameter sets

At every FIPS 205 parameter set, over the approved bundle, the honest readers run on the merged
cache of a relabelled state return drawn cells:

* a state whose only drawn cell is the derivation of one WOTS+ secret, at `x`, reads that secret
  as `x` on its merged cache, and the first step of that chain has its children drawn at `[x]`;
* a settled XMSS root of a reachable tree and a settled FORS public key of a reachable bottom
  position are the drawn labels of their nodes;
* every honest entry is the point of a node at its drawn children values, and every target
  collision of the merged cache is a target collision at a node key.
-/

public section

namespace SLHDSA.LabelReadersTest

open Concrete Security OracleComp OracleSpec

variable {vp : ValidatedParams} (core : CorePrimitives vp.params)

open Classical in
/-- The relabelled state whose only drawn cell is the derivation at the key of the secret of
chain `i` of the WOTS+ instance at `pos`, at the value `x`. -/
noncomputable def secretState (pos : LayerPosition vp) (i : Fin vp.params.len) (x : core.Y) :
    RelabelState (hashSpec core) (DeriveQuery core) (NodeKey core) core.Y :=
  (∅, (∅ : ((DeriveQuery core ⊕ NodeKey core) →ₒ core.Y).QueryCache).cacheQuery
    (.inl (.inl ⟨core.adrsToKey (wotsSkAdrs (wotsInstanceAdrs pos) i.val), _,
      Adrs.isSecretKey_wotsSkAdrs _ _, rfl⟩)) x)

open Classical in
/-- On the merged cache of `secretState`, the oracle-backed secret of chain `i` reads `x`. -/
theorem simulateQ_oracleSecret_secretState (e : core.SkSeed ≃ core.Y) (pkSeed : core.PkSeed)
    (s : core.SkSeed × core.SkPrf) (pos : LayerPosition vp) (i : Fin vp.params.len) (x : core.Y) :
    simulateQ ((secretEncoding core e pkSeed).merge s
        ((slhGraph core pkSeed).toSplitCache (secretState core pos i x))).fst.toPartialImpl
      (oracleSecret core e pkSeed s.1 (wotsSkAdrs (wotsInstanceAdrs pos) i.val)) = some x :=
  (simulateQ_toPartialImpl_oracleSecret_merge (Adrs.isSecretKey_wotsSkAdrs _ _)).trans
    (QueryCache.cacheQuery_self _ _ _)

/-- Under the key discipline, the first step of chain `i` of the WOTS+ instance at `pos` has its
children drawn at `[x]` in `secretState`. -/
theorem childVals_wotsStep_zero_secretState (hd : core.KeyDiscipline vp)
    (e : core.SkSeed ≃ core.Y) (pkSeed : core.PkSeed) (s : core.SkSeed × core.SkPrf)
    (pos : LayerPosition vp) (i : Fin vp.params.len) (x : core.Y) :
    (slhGraph core pkSeed).childVals (secretState core pos i x)
        ⟨core.adrsToKey ((wotsChainAdrs (wotsInstanceAdrs pos) i.val).setHashAddress 0), _,
          wotsChainAdrs_setHashAddress_mem_constructionAddresses pos i
            (Nat.sub_pos_of_lt (Nat.one_lt_two_pow vp.valid.lgw_pos.ne')), rfl⟩ = some [x] :=
  childVals_eq_some_of_chain? (e := e) (s := s) hd
    (wotsChainAdrs_setHashAddress_mem_constructionAddresses pos i
      (Nat.sub_pos_of_lt (Nat.one_lt_two_pow vp.valid.lgw_pos.ne')))
    (simulateQ_oracleSecret_secretState core e pkSeed s pos i x) rfl

/-- At every FIPS 205 parameter set, the first step of a WOTS+ chain whose secret alone is drawn
has its children drawn at the secret. -/
example (ps : FipsParameterSet) (e : (approvedPrimitives ps).core.SkSeed ≃
      (approvedPrimitives ps).core.Y) (pkSeed : (approvedPrimitives ps).core.PkSeed)
    (s : (approvedPrimitives ps).core.SkSeed × (approvedPrimitives ps).core.SkPrf)
    (pos : LayerPosition ps.validatedParams) (i : Fin ps.validatedParams.params.len)
    (x : (approvedPrimitives ps).core.Y) :=
  childVals_wotsStep_zero_secretState _ (keyDiscipline_approvedPrimitives ps) e pkSeed s pos i x

section Readers

variable (e : core.SkSeed ≃ core.Y) (pkSeed : core.PkSeed) (s : core.SkSeed × core.SkPrf)
  (st : RelabelState (hashSpec core) (DeriveQuery core) (NodeKey core) core.Y)

/-- Under the key discipline, a settled XMSS root of a reachable tree is the drawn label of the
root node. -/
theorem label_xmssRoot (hd : core.KeyDiscipline vp) (coord : LayerTreeCoord vp) {v : core.Y}
    (h : xmssRootWithSecret? core ((secretEncoding core e pkSeed).merge s
      ((slhGraph core pkSeed).toSplitCache st)).fst (oracleSecret core e pkSeed s.1) pkSeed
        coord.toAdrs = some v) :
    st.2 (.inr ⟨core.adrsToKey (xmssNodeAdrs coord.toAdrs vp.params.hp 0), _,
      xmssNodeAdrs_mem_constructionAddresses coord vp.valid.hp_pos le_rfl (by simp), rfl⟩) =
        some v :=
  label_of_xmssRootWithSecret? hd
    (xmssNodeAdrs_mem_constructionAddresses coord vp.valid.hp_pos le_rfl (by simp)) h

/-- Under the key discipline, a settled FORS public key of a reachable bottom position is the
drawn label of its roots compression. -/
theorem label_forsPk (hd : core.KeyDiscipline vp) (pos : BottomPosition vp) {v : core.Y}
    (h : forsPkGenWithSecret? core ((secretEncoding core e pkSeed).merge s
      ((slhGraph core pkSeed).toSplitCache st)).fst (oracleSecret core e pkSeed s.1) pkSeed
        pos.forsAdrs = some v) :
    st.2 (.inr ⟨core.adrsToKey (forsPkAdrs pos.forsAdrs), _,
      forsRootAdrs_mem_constructionAddresses pos, rfl⟩) = some v :=
  label_of_forsPkGenWithSecret? hd (forsRootAdrs_mem_constructionAddresses pos) h

/-- Under the key discipline, every honest entry of the merged cache is a node point at drawn
children values. -/
theorem honestEntry_nodePoint (hd : core.KeyDiscipline vp) (t : (publicHashSpec core).Domain)
    (h : HonestEntry (oracleSecret core e pkSeed s.1) pkSeed ((secretEncoding core e
      pkSeed).merge s ((slhGraph core pkSeed).toSplitCache st)).fst t) :
    ∃ κ vs, (slhGraph core pkSeed).childVals st κ = some vs ∧
      (slhGraph core pkSeed).pt κ vs = .inl t :=
  exists_childVals_eq_some_of_honestEntry hd h

/-- Under the key discipline, a target collision of the merged cache is a target collision at a
node key. -/
theorem tcHazard (hd : core.KeyDiscipline vp)
    (h : TargetCollision (oracleSecret core e pkSeed s.1) pkSeed ((secretEncoding core e
      pkSeed).merge s ((slhGraph core pkSeed).toSplitCache st)).fst) :
    (slhNodeKeys core pkSeed).TCHazard st :=
  tcHazard_of_targetCollision hd h

end Readers

/-- At every FIPS 205 parameter set, a settled XMSS root of a reachable tree is a drawn label. -/
example (ps : FipsParameterSet) :=
  label_xmssRoot (vp := ps.validatedParams) _ (hd := keyDiscipline_approvedPrimitives ps)

/-- At every FIPS 205 parameter set, a settled FORS public key of a reachable bottom position is
a drawn label. -/
example (ps : FipsParameterSet) :=
  label_forsPk (vp := ps.validatedParams) _ (hd := keyDiscipline_approvedPrimitives ps)

/-- At every FIPS 205 parameter set, every honest entry of the merged cache is a node point at
drawn children values. -/
example (ps : FipsParameterSet) :=
  honestEntry_nodePoint (vp := ps.validatedParams) _ (hd := keyDiscipline_approvedPrimitives ps)

/-- At every FIPS 205 parameter set, a target collision of the merged cache is a target collision
at a node key of the relabelled state. -/
example (ps : FipsParameterSet) :=
  tcHazard (vp := ps.validatedParams) _ (hd := keyDiscipline_approvedPrimitives ps)

end SLHDSA.LabelReadersTest
