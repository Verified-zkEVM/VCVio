/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.Security.Transport

/-!
# A completed public miss at the FIPS 205 parameter sets

At every FIPS 205 parameter set, over the approved bundle, take a state whose public cache holds
the point of the first hash step of a WOTS+ chain at the input `[x]` and whose cells are all
undrawn, and the state with the same public cache in which the chain's secret is drawn at `x`. The
first state's cache reads the public entry at that point, because the step's only child is
undrawn; the second state is a conflict, because the step's children are drawn at `[x]` and the
public cache holds its point there. The conflict is derived from the honest chain read after the
fill, with no reference to the definition of a conflict.
-/

public section

namespace SLHDSA.TransportTest

open Concrete Security OracleComp OracleSpec

variable {vp : ValidatedParams} (core : CorePrimitives vp.params)

/-- The first step of a WOTS+ chain lies below the top step `w - 1`. -/
theorem zero_lt_w_sub_one : 0 < vp.params.w - 1 :=
  Nat.sub_pos_of_lt (Nat.one_lt_two_pow vp.valid.lgw_pos.ne')

/-- The node of the first hash step of chain `i` of the WOTS+ instance at `pos`. -/
def firstStep (pos : LayerPosition vp) (i : Fin vp.params.len) : NodeKey core :=
  ⟨core.adrsToKey ((wotsChainAdrs (wotsInstanceAdrs pos) i.val).setHashAddress 0), _,
    wotsChainAdrs_setHashAddress_mem_constructionAddresses pos i zero_lt_w_sub_one, rfl⟩

/-- The cell of the secret of chain `i` of the WOTS+ instance at `pos`. -/
def secretCell (pos : LayerPosition vp) (i : Fin vp.params.len) : DeriveQuery core ⊕ NodeKey core :=
  .inl (.inl ⟨core.adrsToKey (wotsSkAdrs (wotsInstanceAdrs pos) i.val), _,
    Adrs.isSecretKey_wotsSkAdrs _ _, rfl⟩)

open Classical in
/-- The public cache holding the point of `firstStep` at `[x]`, answered `y`. -/
noncomputable def missCache (pkSeed : core.PkSeed) (pos : LayerPosition vp)
    (i : Fin vp.params.len) (x y : core.Y) : (hashSpec core).QueryCache :=
  (∅ : (hashSpec core).QueryCache).cacheQuery (.inl (.thash pkSeed (firstStep core pos i).1 [x])) y

/-- Before the fill: the public miss, and no drawn cell. -/
noncomputable def missState (pkSeed : core.PkSeed) (pos : LayerPosition vp)
    (i : Fin vp.params.len) (x y : core.Y) : LabState core :=
  (missCache core pkSeed pos i x y, ∅)

open Classical in
/-- After the fill: the same public cache, and the chain's secret drawn at `x`. -/
noncomputable def filledState (pkSeed : core.PkSeed) (pos : LayerPosition vp)
    (i : Fin vp.params.len) (x y : core.Y) : LabState core :=
  (missCache core pkSeed pos i x y,
    (∅ : ((DeriveQuery core ⊕ NodeKey core) →ₒ core.Y).QueryCache).cacheQuery
      (secretCell core pos i) x)

/-- Under the key discipline, the cell of the chain's secret is the only child of its first
step. -/
theorem pathCell_zero_eq_secretCell (pos : LayerPosition vp) (i : Fin vp.params.len) :
    pathCell core (wotsSkAdrs (wotsInstanceAdrs pos) i.val)
      ((wotsChainAdrs (wotsInstanceAdrs pos) i.val).setHashAddress ·) 0 =
        some (secretCell core pos i) :=
  pathCell_zero core (Adrs.isSecretKey_wotsSkAdrs _ _) _

open Classical in
/-- Under the key discipline, before the fill the cache of `missState` reads the public entry at
the first step's point. -/
theorem merge_fst_missState (hd : core.KeyDiscipline vp) (e : core.SkSeed ≃ core.Y)
    (pkSeed : core.PkSeed) (s : core.SkSeed × core.SkPrf) (pos : LayerPosition vp)
    (i : Fin vp.params.len) (x y : core.Y) :
    ((secretEncoding core e pkSeed).merge s
      ((slhGraph core pkSeed).toSplitCache (missState core pkSeed pos i x y))).fst
        (.thash pkSeed (firstStep core pos i).1 [x]) = some y := by
  refine (merge_fst_thash_of_childVals_ne hd.keySeparated fun h ↦ ?_).trans
    (QueryCache.cacheQuery_self _ _ _)
  have := (slhGraph core pkSeed).isSome_childVals_iff.1 (Option.isSome_of_eq_some h)
    (secretCell core pos i) (by
    rw [firstStep, slhGraph_ch_wotsChainAdrs_setHashAddress core hd pkSeed
      (wotsChainAdrs_setHashAddress_mem_constructionAddresses pos i zero_lt_w_sub_one),
      pathCell_zero_eq_secretCell]
    exact List.mem_singleton_self _)
  simp [missState] at this

open Classical in
/-- **A completed public miss.** Under the key discipline, `filledState` is a conflict: the
honest chain of length `0` from the secret read on its cache reaches `x`, whose cell is undrawn
in `missState`, and the cache of `missState` holds the first step's point at `[x]`. -/
theorem conflict_filledState (hd : core.KeyDiscipline vp) (e : core.SkSeed ≃ core.Y)
    (pkSeed : core.PkSeed) (s : core.SkSeed × core.SkPrf) (pos : LayerPosition vp)
    (i : Fin vp.params.len) (x y : core.Y) :
    (slhGraph core pkSeed).Conflict (filledState core pkSeed pos i x y) :=
  conflict_of_chain?_of_cell_eq_none (e := e) (s := s) (st₀ := missState core pkSeed pos i x y)
    hd le_rfl (wotsChainAdrs_setHashAddress_mem_constructionAddresses pos i zero_lt_w_sub_one)
    (pathCell_zero_eq_secretCell core pos i) rfl
    (by rw [show core.adrsToKey ((wotsChainAdrs (wotsInstanceAdrs pos) i.val).setHashAddress 0) =
        (firstStep core pos i).1 from rfl, merge_fst_missState core hd]; rfl)
    ((simulateQ_toPartialImpl_oracleSecret_merge (Adrs.isSecretKey_wotsSkAdrs _ _)).trans
      (QueryCache.cacheQuery_self _ _ _)) rfl

/-- At every FIPS 205 parameter set, a WOTS+ chain secret drawn by the fill at a value whose first
hash step the public cache already holds is a conflict. -/
example (ps : FipsParameterSet) (e : (approvedPrimitives ps).core.SkSeed ≃
      (approvedPrimitives ps).core.Y) (pkSeed : (approvedPrimitives ps).core.PkSeed)
    (s : (approvedPrimitives ps).core.SkSeed × (approvedPrimitives ps).core.SkPrf)
    (pos : LayerPosition ps.validatedParams) (i : Fin ps.validatedParams.params.len)
    (x y : (approvedPrimitives ps).core.Y) :
    (slhGraph (vp := ps.validatedParams) (approvedPrimitives ps).core pkSeed).Conflict
      (filledState (approvedPrimitives ps).core pkSeed pos i x y) :=
  conflict_filledState _ (keyDiscipline_approvedPrimitives ps) e pkSeed s pos i x y

end SLHDSA.TransportTest
