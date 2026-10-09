/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.Security.Transport
public import HashSig.SLHDSA.Security.KeyDiscipline
public import HashSigTest.SLHDSA.Bundles

/-!
# Hidden cells of the deferred lab experiment

* **The forgery's hidden values are undrawn before the fill.** Let `st₀` be a state whose hidden
  cells are undrawn for the digests a transcript's log signs, and `st` a larger state with the
  same public cache. A WOTS+ chain value that the replay of a forgery, read off the merged cache
  of `st`, finds hidden has an undrawn cell in `st₀`, and so does an unopened FORS secret. At
  every SHAKE bundle whose address fields fit their FIPS 205 widths, the final state of every run
  of the deferred lab experiment is such an `st₀` for the filled transcript.
* **Hidden cells exist.** With no signed digest, the cell of the secret of every WOTS+ chain at
  every position is hidden; at every FIPS 205 parameter set this holds over the approved bundle.
* **The invariant can fail.** A state that has drawn such a secret, with an empty log, does not
  satisfy `HiddenUndrawn`.
-/

public section

open OracleComp OracleSpec SignatureAlg

namespace SLHDSA.HiddenUndrawnTest

open Concrete Security BundleTest
open scoped MergedCache

variable {vp : ValidatedParams} {core : CorePrimitives vp.params} {e : core.SkSeed ≃ core.Y}
  {pkSeed : core.PkSeed} {s : core.SkSeed × core.SkPrf}

/-! ## The forgery's hidden values -/

/-- At every SHAKE bundle whose address fields fit their widths, a WOTS+ chain value that the
replay of a forgery, read off the merged cache of a state `st` above the final state of a run of
the deferred lab experiment with the same public cache, finds hidden is undrawn in the final
state. -/
example (vp : ValidatedParams) (hb : CanonicalAddressBounds vp.params)
    {e : (shakeCore vp).SkSeed ≃ (shakeCore vp).Y}
    {optRand : PublicKeyCore (shakeCore vp) → ProbComp (shakeCore vp).Y}
    {pkSeed : (shakeCore vp).PkSeed}
    {adv : UnforgeableAdversary (romScheme (shakeCore vp) e optRand (pure pkSeed))}
    (s : (shakeCore vp).SkSeed × (shakeCore vp).SkPrf) {z}
    (hz : z ∈ support ((simulateQ (slhGraph (shakeCore vp) pkSeed).deferredImpl
      (labExperiment (shakeCore vp) adv pkSeed)).run ((∅, ∅), [])))
    {st : RelabelState (hashSpec (shakeCore vp)) (DeriveQuery (shakeCore vp))
      (NodeKey (shakeCore vp)) (shakeCore vp).Y}
    (hle : z.2.1 ≤ st) (hfst : st.1 = z.2.1.1)
    {j : Fin vp.params.d} {pos : LayerPosition vp} {m : (shakeCore vp).Y}
    {i : Fin vp.params.len}
    (hFL : ForgerLayer (DeriveOutcome.fill _ s z.1) 𝒞[e, pkSeed, s, st] j pos m)
    (hHCV : HiddenChainValue (oracleSecret _ e (DeriveOutcome.fill _ s z.1).pk.pkSeed
      (DeriveOutcome.fill _ s z.1).sk.skSeed) (DeriveOutcome.fill _ s z.1) 𝒞[e, pkSeed, s, st]
      j pos i.val (chainStepsCore _ m i.val))
    (ht : chainStepsCore _ m i.val < vp.params.w - 1) :
    ∃ c, childCell _ (chainChild pos i.val (chainStepsCore _ m i.val)) = some c ∧
      z.2.1.2 c = none :=
  have h := hiddenUndrawn_of_mem_support_deferredImpl_labExperiment pkSeed
    (keyDiscipline_shakePrimitives vp hb) adv hz
  exists_cell_chainChild_eq_none_of_hiddenChainValue (keyDiscipline_shakePrimitives vp hb) hle hfst
    (by simpa [DeriveOutcome.fill] using h.1) (by simp [DeriveOutcome.fill, fillSecretKey])
    (by simpa [DeriveOutcome.fill] using h.2) hFL hHCV ht

/-- At every SHAKE bundle, an unopened FORS secret of the replay of a forgery is undrawn in the
final state of every run of the deferred lab experiment. -/
example (vp : ValidatedParams) (hb : CanonicalAddressBounds vp.params)
    {e : (shakeCore vp).SkSeed ≃ (shakeCore vp).Y}
    {optRand : PublicKeyCore (shakeCore vp) → ProbComp (shakeCore vp).Y}
    {pkSeed : (shakeCore vp).PkSeed}
    {adv : UnforgeableAdversary (romScheme (shakeCore vp) e optRand (pure pkSeed))}
    (s : (shakeCore vp).SkSeed × (shakeCore vp).SkPrf) {z}
    (hz : z ∈ support ((simulateQ (slhGraph (shakeCore vp) pkSeed).deferredImpl
      (labExperiment (shakeCore vp) adv pkSeed)).run ((∅, ∅), [])))
    {st : RelabelState (hashSpec (shakeCore vp)) (DeriveQuery (shakeCore vp))
      (NodeKey (shakeCore vp)) (shakeCore vp).Y}
    (hfst : st.1 = z.2.1.1) {digest : Bytes vp.params.m} {i : Fin vp.params.k}
    (hUC : UnopenedCoord (DeriveOutcome.fill _ s z.1) 𝒞[e, pkSeed, s, st]
      (splitDigest vp.params digest).forsAdrs
      (forsSigLeafIndex vp.params (splitDigest vp.params digest).md.toList i.val)) :
    ∃ c, childCell _ (.inl (forsSkAdrs (splitDigest vp.params digest).forsAdrs
        (forsSigLeafIndex vp.params (splitDigest vp.params digest).md.toList i.val))) = some c ∧
      z.2.1.2 c = none :=
  exists_cell_forsSkAdrs_eq_none_of_unopenedCoord hfst (by simpa [DeriveOutcome.fill] using
    (hiddenUndrawn_of_mem_support_deferredImpl_labExperiment pkSeed
      (keyDiscipline_shakePrimitives vp hb) adv hz).2) hUC

/-! ## Hidden cells exist, and the invariant can fail -/

variable (core) in
/-- The cell of the secret of WOTS+ chain `i` at `pos`. -/
abbrev wotsSkCell (pos : LayerPosition vp) (i : Fin vp.params.len) :
    DeriveQuery core ⊕ NodeKey core :=
  .inl (.inl ⟨core.adrsToKey (wotsSkAdrs (wotsInstanceAdrs pos) i.val), _,
    Adrs.isSecretKey_wotsSkAdrs _ _, rfl⟩)

/-- With no signed digest, the secret of every WOTS+ chain at every position is a hidden cell. -/
theorem wotsSkCell_mem_hiddenCells (pos : LayerPosition vp) (i : Fin vp.params.len)
    {U : Bytes vp.params.m → Prop} (hU : ∀ d, ¬U d)
    (st : RelabelState (hashSpec core) (DeriveQuery core) (NodeKey core) core.Y) :
    wotsSkCell core pos i ∈ hiddenCells core U st :=
  mem_hiddenCells_of_hiddenChainStep (t := 0)
    ⟨by have : 2 ≤ vp.params.w := Nat.one_lt_two_pow vp.valid.lgw_pos.ne'; omega,
      fun ⟨d, hd, _⟩ ↦ (hU d hd).elim⟩
    (childCell_inl core (Adrs.isSecretKey_wotsSkAdrs _ _))

/-- A state that has drawn the secret of a WOTS+ chain does not satisfy the invariant for an
empty log. -/
theorem not_hiddenUndrawn_nil (pk : PublicKeyCore core) (pos : LayerPosition vp)
    (i : Fin vp.params.len)
    {st : RelabelState (hashSpec core) (DeriveQuery core) (NodeKey core) core.Y} {v : core.Y}
    (h : st.2 (wotsSkCell core pos i) = some v) : ¬HiddenUndrawn core pk [] st := fun hu ↦ by
  have := hu _ (wotsSkCell_mem_hiddenCells pos i (fun _ ⟨_, he, _⟩ ↦ by simp at he) st)
  simp [h] at this

/-- At every FIPS 205 parameter set, over the approved bundle, the secret of every WOTS+ chain at
the bottom position of every digest is hidden while no digest is signed. -/
example (ps : FipsParameterSet) (parts : DigestParts ps.validatedParams.params)
    (i : Fin ps.validatedParams.params.len)
    (st : RelabelState (hashSpec (approvedPrimitives ps).core)
      (DeriveQuery (vp := ps.validatedParams) (approvedPrimitives ps).core)
      (NodeKey (vp := ps.validatedParams) (approvedPrimitives ps).core)
      (approvedPrimitives ps).core.Y) :
    wotsSkCell _ (LayerPosition.initial ps.validatedParams parts) i ∈
      hiddenCells (vp := ps.validatedParams) _ (fun _ ↦ False) st :=
  wotsSkCell_mem_hiddenCells _ i (fun _ h ↦ h) st

/-- At every SHAKE bundle, the state that has drawn only the secret of a WOTS+ chain does not
satisfy the invariant for an empty log. -/
example (vp : ValidatedParams) (pk : PublicKeyCore (shakeCore vp)) (pos : LayerPosition vp)
    (i : Fin vp.params.len) (v : (shakeCore vp).Y) :
    ¬HiddenUndrawn (shakeCore vp) pk []
      (∅, (∅ : ((DeriveQuery (shakeCore vp) ⊕ NodeKey (shakeCore vp)) →ₒ
        (shakeCore vp).Y).QueryCache).cacheQuery (wotsSkCell _ pos i) v) :=
  not_hiddenUndrawn_nil pk pos i (QueryCache.cacheQuery_self _ _ _)

end SLHDSA.HiddenUndrawnTest
