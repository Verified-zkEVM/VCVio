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
* once the label `y` of that first step is drawn too, the chain reads `y` after one step, the
  second step has its children drawn at `[y]`, and the first step's key at any other input reads
  the empty public cache;
* a settled XMSS root of a reachable tree, a settled FORS public key of a reachable bottom
  position and the honest message at a layer-zero position are the drawn labels of their nodes;
* the `H_msg` points of the merged cache read the public cache.
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

/-- The first step of a WOTS+ chain lies below the top step `w - 1`. -/
theorem zero_lt_w_sub_one : 0 < vp.params.w - 1 :=
  Nat.sub_pos_of_lt (Nat.one_lt_two_pow vp.valid.lgw_pos.ne')

/-- The node of step `t < w - 1` of chain `i` of the WOTS+ instance at `pos`. -/
def stepKey (pos : LayerPosition vp) (i : Fin vp.params.len) (t : ℕ)
    (ht : t < vp.params.w - 1) : NodeKey core :=
  ⟨core.adrsToKey ((wotsChainAdrs (wotsInstanceAdrs pos) i.val).setHashAddress t), _,
    wotsChainAdrs_setHashAddress_mem_constructionAddresses pos i ht, rfl⟩

open Classical in
/-- `secretState` with the label of the first step of chain `i` also drawn, at the value `y`. -/
noncomputable def chainState (pos : LayerPosition vp) (i : Fin vp.params.len) (x y : core.Y) :
    RelabelState (hashSpec core) (DeriveQuery core) (NodeKey core) core.Y :=
  (∅, (secretState core pos i x).2.cacheQuery (.inr (stepKey core pos i 0 zero_lt_w_sub_one)) y)

section ChainState

variable (hd : core.KeyDiscipline vp) (e : core.SkSeed ≃ core.Y) (pkSeed : core.PkSeed)
  (s : core.SkSeed × core.SkPrf) (pos : LayerPosition vp) (i : Fin vp.params.len) (x y : core.Y)

include hd e s in
open Classical in
/-- In `chainState`, the first step of chain `i` has its children drawn at `[x]`. -/
theorem childVals_stepKey_zero_chainState :
    (slhGraph core pkSeed).childVals (chainState core pos i x y)
      (stepKey core pos i 0 zero_lt_w_sub_one) = some [x] :=
  childVals_eq_some_of_chain? (e := e) (s := s) hd
    (wotsChainAdrs_setHashAddress_mem_constructionAddresses pos i zero_lt_w_sub_one)
    ((simulateQ_toPartialImpl_oracleSecret_merge (Adrs.isSecretKey_wotsSkAdrs _ _)).trans
      ((QueryCache.cacheQuery_of_ne _ _ Sum.inl_ne_inr).trans (QueryCache.cacheQuery_self _ _ _)))
    rfl

include hd in
open Classical in
/-- On the merged cache of `chainState`, the chain of `i` from the secret reads the drawn label
`y` after one step: the point of the first step at the secret is that step's point at its drawn
children values. -/
theorem chain?_one_chainState :
    chain? core ((secretEncoding core e pkSeed).merge s
        ((slhGraph core pkSeed).toSplitCache (chainState core pos i x y))).fst pkSeed
      (wotsChainAdrs (wotsInstanceAdrs pos) i.val) x 0 1 = some y :=
  (chain?_succ_eq_some_iff core _ pkSeed _ x 0 0).2 ⟨x, rfl,
    (merge_fst_thash_of_childVals_eq_some hd.keySeparated
      (childVals_stepKey_zero_chainState core hd e pkSeed s pos i x y)).trans
      (QueryCache.cacheQuery_self _ _ _)⟩

include hd e s in
open Classical in
/-- Under the key discipline, at `w ≥ 3`, the second step of chain `i` has its children drawn
at the label `y` of the first step in `chainState`. -/
theorem childVals_stepKey_one_chainState (hw : 1 < vp.params.w - 1) :
    (slhGraph core pkSeed).childVals (chainState core pos i x y) (stepKey core pos i 1 hw) =
      some [y] :=
  childVals_eq_some_of_chain? (e := e) (s := s) hd
    (wotsChainAdrs_setHashAddress_mem_constructionAddresses pos i hw)
    ((simulateQ_toPartialImpl_oracleSecret_merge (Adrs.isSecretKey_wotsSkAdrs _ _)).trans
      ((QueryCache.cacheQuery_of_ne _ _ Sum.inl_ne_inr).trans (QueryCache.cacheQuery_self _ _ _)))
    (chain?_one_chainState core hd e pkSeed s pos i x y)

include hd in
open Classical in
/-- On the merged cache of `chainState`, the first step's key at an input other than `[x]` reads
the empty public cache. -/
theorem merge_fst_stepKey_of_ne_chainState {ys : List core.Y} (hys : [x] ≠ ys) :
    ((secretEncoding core e pkSeed).merge s
        ((slhGraph core pkSeed).toSplitCache (chainState core pos i x y))).fst
      (.thash pkSeed (stepKey core pos i 0 zero_lt_w_sub_one).1 ys) = none :=
  (merge_fst_thash_of_childVals_eq_some_of_ne hd.keySeparated
    (childVals_stepKey_zero_chainState core hd e pkSeed s pos i x y) hys).trans
    (QueryCache.empty_apply _)

end ChainState

/-- At every FIPS 205 parameter set, the second step of a WOTS+ chain whose secret and first
step alone are drawn has its children drawn at the first step's label. -/
example (ps : FipsParameterSet) (e : (approvedPrimitives ps).core.SkSeed ≃
      (approvedPrimitives ps).core.Y) (pkSeed : (approvedPrimitives ps).core.PkSeed)
    (s : (approvedPrimitives ps).core.SkSeed × (approvedPrimitives ps).core.SkPrf)
    (pos : LayerPosition ps.validatedParams) (i : Fin ps.validatedParams.params.len)
    (x y : (approvedPrimitives ps).core.Y) (hw : 1 < ps.validatedParams.params.w - 1) :=
  childVals_stepKey_one_chainState _ (keyDiscipline_approvedPrimitives ps) e pkSeed s pos i x y hw

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

/-- Every `H_msg` point of the merged cache of the empty state is unset. -/
example (r : core.Y) (pk : core.PkSeed) (root : core.Y) (msg : List Byte) :
    ((secretEncoding core e pkSeed).merge s ((slhGraph core pkSeed).toSplitCache
      ((∅, ∅) : RelabelState (hashSpec core) (DeriveQuery core) (NodeKey core) core.Y))).fst
        (.hmsg r pk root msg) = none :=
  (merge_fst_hmsg r pk root msg).trans (QueryCache.empty_apply _)

end Readers

/-- At every FIPS 205 parameter set, a settled XMSS root of a reachable tree is a drawn label. -/
example (ps : FipsParameterSet) :=
  label_xmssRoot (vp := ps.validatedParams) _ (hd := keyDiscipline_approvedPrimitives ps)

/-- At every FIPS 205 parameter set, a settled FORS public key of a reachable bottom position is
a drawn label. -/
example (ps : FipsParameterSet) :=
  label_forsPk (vp := ps.validatedParams) _ (hd := keyDiscipline_approvedPrimitives ps)

/-- At every FIPS 205 parameter set, the honest message signed at a layer-zero position is the
drawn label of the FORS roots compression of its instance. -/
example (ps : FipsParameterSet) {e : (approvedPrimitives ps).core.SkSeed ≃
      (approvedPrimitives ps).core.Y} {pkSeed : (approvedPrimitives ps).core.PkSeed}
    {s : (approvedPrimitives ps).core.SkSeed × (approvedPrimitives ps).core.SkPrf}
    {st : RelabelState (hashSpec (approvedPrimitives ps).core) (DeriveQuery _) (NodeKey _) _}
    (pos : LayerPosition ps.validatedParams) (h0 : pos.layer.val = 0) {m : _}
    (h : honestMessage? ((secretEncoding _ e pkSeed).merge s
      ((slhGraph _ pkSeed).toSplitCache st)).fst (oracleSecret _ e pkSeed s.1) pkSeed pos =
        some m) :
    st.2 (.inr ⟨_, _, forsPkAdrs_forsInstanceAdrs_mem_constructionAddresses pos h0, rfl⟩) =
      some m :=
  Eq.trans (by congr 3; simp [msgAdrs, h0])
    (label_of_honestMessage? (keyDiscipline_approvedPrimitives ps) pos h)

end SLHDSA.LabelReadersTest
