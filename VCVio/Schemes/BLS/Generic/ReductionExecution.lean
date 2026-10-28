/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.Schemes.BLS.Generic.Cache
public import VCVio.CryptoFoundations.GroupModel.PairingExecution
import all VCVio.CryptoFoundations.GroupModel.Instances
import all VCVio.Schemes.BLS.Generic.ReductionPrograms

/-! # Real execution of BLS extraction handlers

The real handler retains source representations and chronological reply labels. The relation
to a generic execution also records private-handle validity and the visible real table.
-/

public section

open OracleComp OracleSpec GroupModel GroupModel.Interaction

namespace BLS.Generic

variable {F M R T : Type} {G : Bool → Type}

attribute [local implicit_reducible] spec handleSpec PFam

/-- Real tracked tables and chronological hash/signing occurrences. -/
abbrev RealReductionState (F M : Type) (G : Bool → Type) (T : Type) :=
  Pairing.Tracked F G T × LinearFunctional.Transcript M

/-- Real scalar lookup and chronological receipts for the extraction handler. -/
@[expose] def realReductionHandler [CommSemiring F]
    [∀ b, AddCommMonoid (G b)] [∀ b, Module F (G b)] [∀ b, DecidableEq (G b)]
    [AddCommMonoid T] [Module F T] [DecidableEq T]
    (e : G false →ₗ[F] G true →ₗ[F] T) (hash sign : R → G false) :
    QueryImpl (adversarySpec F M)
      (StateT (RealReductionState F M G T) (OracleComp (unifSpec + (M →ₒ R))))
  | .inl q => fun st => pure ((Pairing.step e q st.1).1, (Pairing.step e q st.1).2, st.2)
  | .inr (.inl _) => fun st => pure ((), st)
  | .inr (.inr (.inl n)) => fun st => do
      let a ← (unifSpec + (M →ₒ R)).query (.inl n)
      return (a, st)
  | .inr (.inr (.inr q)) => fun st => do
      let (kind, m) := match q.data with | .inl m => (false, m) | .inr m => (true, m)
      let r ← (unifSpec + (M →ₒ R)).query (.inr m)
      let value := if kind then sign r else hash r
      return (⟨(), fun | .g₁ => [(st.1.1.2 false).length] | .g₂ => [] | .gₜ => []⟩,
        (receive st.1.1 (fun | false => [value] | true => []), st.1.2), st.2 ++ [(kind, m)])

/-- Information used by the scalar extractor: target message, coefficient list, and reply labels. -/
@[expose] def reductionView [Zero F]
    (out : Message M (fun _ : PSort => Handle)) (st : ReductionState F M) :
    M × List F × LinearFunctional.Transcript M :=
  (out.data, ((explain st.metadata.1 (Pairing.sourceMessage out)).coefficients false).headD [],
    st.transcript)

/-- The real tracked execution exposes exactly the same extraction information. -/
@[expose] def realReductionView [Zero F] [∀ b, Zero (G b)]
    (out : Message M (fun _ : PSort => Handle)) (st : RealReductionState F M G T) :
    M × List F × LinearFunctional.Transcript M :=
  (out.data, ((explain st.1.1 (Pairing.sourceMessage out)).coefficients false).headD [], st.2)

/-- A generic reduction state and a real tracked state describe the same visible computation. -/
structure ReductionRelated [Zero F] [∀ b, AddCommMonoid (G b)] [AddCommMonoid T]
    (root : Tbl (PFam (G false) (G true) T)) (z : PSort → Handle)
    (st : ReductionState F M) (tbl : Tbl (PFam (G false) (G true) T))
    (real : RealReductionState F M G T) : Prop where
  /-- Challenge inputs remain an outer-table prefix. -/
  extendsRoot : ∀ s, root s <+: tbl s
  /-- Local and zero handles refer to valid outer entries. -/
  valid : WellFormed z st.handles tbl
  /-- Real and scalar-only trackers retain identical coefficients. -/
  metadata : st.metadata = Pairing.eraseValues real.1
  /-- The virtual table reads back to the real tracker's values. -/
  values : readBack st.handles tbl = Pairing.table real.1
  /-- Reply occurrences agree in kind, label, and order. -/
  transcript : st.transcript = real.2

/-- Related executions give identical scalar-extraction inputs. -/
theorem ReductionRelated.view_eq [Zero F] [∀ b, AddCommMonoid (G b)] [AddCommMonoid T]
    {root : Tbl (PFam (G false) (G true) T)} {z : PSort → Handle}
    {st : ReductionState F M} {tbl : Tbl (PFam (G false) (G true) T)}
    {real : RealReductionState F M G T} (h : ReductionRelated root z st tbl real)
    (out : Message M (fun _ : PSort => Handle)) :
    reductionView out st = realReductionView out real := by
  simp only [reductionView, realReductionView, h.metadata, Pairing.eraseValues,
    Pairing.explain_eraseSourceValues_coefficients, h.transcript]

/-- A visible source handle table and its real tracker always have the same length. -/
theorem ReductionRelated.source_length [Zero F] [∀ b, AddCommMonoid (G b)] [AddCommMonoid T]
    {root : Tbl (PFam (G false) (G true) T)} {z : PSort → Handle}
    {st : ReductionState F M} {tbl : Tbl (PFam (G false) (G true) T)}
    {real : RealReductionState F M G T} (h : ReductionRelated root z st tbl real) :
    (st.handles .g₁).length = (real.1.1.2 false).length := by
  have he := congrArg List.length (congrFun h.values .g₁)
  simpa only [readBack, Pairing.table, List.length_map] using he

/-- A virtualized group step preserves the full execution relation and its actual reply. -/
theorem ReductionRelated.group [CommSemiring F] [DecidableEq F]
    [∀ b, AddCommMonoid (G b)] [∀ b, Module F (G b)] [∀ b, DecidableEq (G b)]
    [AddCommMonoid T] [Module F T] [DecidableEq T]
    [∀ s, DecidableEq (PFam (G false) (G true) T s)]
    (e : G false →ₗ[F] G true →ₗ[F] T)
    {root : Tbl (PFam (G false) (G true) T)} {z : PSort → Handle}
    {st : ReductionState F M} {tbl : Tbl (PFam (G false) (G true) T)}
    {real : RealReductionState F M G T} (h : ReductionRelated root z st tbl real)
    (q : GroupModel.Query F pairingSig)
    (r : ((spec F pairingSig).Range q × Tbl (fun _ : PSort => Handle)) ×
      Tbl (PFam (G false) (G true) T))
    (hr : runGen (pairingReal e) (fun _ => id)
      ((virtualizeImpl z (.inl q)).run st.handles) tbl = pure r) :
    r.1.1 = (Pairing.step e q real.1).1 ∧
      ReductionRelated root z
        ⟨r.1.2, (Pairing.step (0 : F →ₗ[F] F →ₗ[F] F) q st.metadata).2, st.transcript⟩
        r.2 ((Pairing.step e q real.1).2, real.2) := by
  have hs : r ∈ support (runGen (pairingReal e) (fun _ => id)
      ((virtualizeImpl z (.inl q)).run st.handles) tbl) := by rw [hr]; simp
  have he := virtualize_step_readBack (pairingReal e) (fun _ => id) h.valid (.inl q)
  rw [h.values, hr, map_pure] at he
  have hd : runGen (pairingReal e) (fun _ => id)
      (liftM ((genSpec F pairingSig).query (.inl q))) (Pairing.table real.1) =
      pure ((Pairing.step e q real.1).1, Pairing.table (Pairing.step e q real.1).2) := by
    simp only [runGen, run, simulateQ_spec_query, QueryImpl.add_apply_inl]
    exact Pairing.step_projection e q real.1
  rw [hd] at he
  have heq : ((Pairing.step e q real.1).1, Pairing.table (Pairing.step e q real.1).2) =
      (r.1.1, readBack r.1.2 r.2) := by simpa only [pure_inj] using he
  refine ⟨(congrArg Prod.fst heq).symm, ?_⟩
  constructor
  · intro s
    exact (h.extendsRoot s).trans (runGen_prefix (pairingReal e) (fun _ => id) _ _ r hs s)
  · exact virtualize_step_wellFormed (pairingReal e) (fun _ => id) h.valid (.inl q) r hs
  · simpa only [h.metadata] using (Pairing.eraseValues_step e q real.1).symm
  · exact (congrArg Prod.snd heq).symm
  · exact h.transcript

/-- Installing a valid outer point preserves coefficients and chronological reply information. -/
theorem ReductionRelated.receive [CommSemiring F]
    [∀ b, AddCommMonoid (G b)] [AddCommMonoid T]
    {root : Tbl (PFam (G false) (G true) T)} {z : PSort → Handle}
    {st : ReductionState F M} {tbl tbl' : Tbl (PFam (G false) (G true) T)}
    {real : RealReductionState F M G T} (h : ReductionRelated root z st tbl real)
    (hp : ∀ s, tbl s <+: tbl' s) (handle : Handle) (hh : handle < (tbl' .g₁).length)
    (kind : Bool) (m : M) (value : G false) (hv : lookup tbl' .g₁ handle = value) :
    ReductionRelated root z (reductionReceive st kind m handle) tbl'
      ((receive real.1.1 (fun | false => [value] | true => []), real.1.2),
        real.2 ++ [(kind, m)]) := by
  constructor
  · intro s
    exact (h.extendsRoot s).trans (hp s)
  · exact wellFormed_receive h.valid hp .g₁ handle hh
  · simp only [reductionReceive, h.metadata, Pairing.eraseValues]
    congr 1
    rw [Pairing.eraseSourceValues_receive]
    congr 1
    funext b
    cases b <;> rfl
  · change readBack (append st.handles .g₁ handle) tbl' = _
    rw [readBack_receive h.valid hp, hv, h.values, Pairing.table_receive]
    funext s
    cases s <;> simp [pushGroups, Pairing.pairingMessage, append]
  · simp only [reductionReceive, h.transcript]

/-- A point program deterministically returns a valid first-source point and extends the table. -/
@[expose] def RealizesPoint [CommSemiring F]
    [∀ b, AddCommMonoid (G b)] [∀ b, Module F (G b)]
    [AddCommMonoid T] [Module F T]
    [∀ s, DecidableEq (PFam (G false) (G true) T s)]
    (e : G false →ₗ[F] G true →ₗ[F] T)
    (root : Tbl (PFam (G false) (G true) T))
    (program : R → OracleComp (genSpec F pairingSig) Handle) (value : R → G false) : Prop :=
  ∀ r tbl, (∀ s, root s <+: tbl s) → ∃ h tbl',
    runGen (pairingReal e) (fun _ => id) (program r) tbl = pure (h, tbl') ∧
    (∀ s, tbl s <+: tbl' s) ∧ h < (tbl' .g₁).length ∧ lookup tbl' .g₁ h = value r

private def combinedHandler [CommSemiring F] [DecidableEq F]
    [∀ b, AddCommMonoid (G b)] [∀ b, Module F (G b)]
    [AddCommMonoid T] [Module F T]
    [∀ s, DecidableEq (PFam (G false) (G true) T s)]
    (e : G false →ₗ[F] G true →ₗ[F] T) (z : PSort → Handle)
    (hash sign : R → OracleComp (genSpec F pairingSig) Handle) :
    QueryImpl (adversarySpec F M)
      (StateT (ReductionState F M × Tbl (PFam (G false) (G true) T))
        (OracleComp (unifSpec + (M →ₒ R))))
  | .inl q => fun (st, tbl) => do
      let r ← liftM (runGen (pairingReal e) (fun _ => id)
        ((virtualizeImpl z (.inl q)).run st.handles) tbl)
      return (r.1.1, ⟨r.1.2, (Pairing.step (0 : F →ₗ[F] F →ₗ[F] F) q st.metadata).2,
        st.transcript⟩, r.2)
  | .inr (.inl _) => fun st => pure ((), st)
  | .inr (.inr (.inl n)) => fun st => do
      let r ← (unifSpec + (M →ₒ R)).query (.inl n)
      return (r, st)
  | .inr (.inr (.inr q)) => fun (st, tbl) => do
      let (kind, m) := match q.data with | .inl m => (false, m) | .inr m => (true, m)
      let r ← (unifSpec + (M →ₒ R)).query (.inr m)
      let (h, tbl') ← liftM (runGen (pairingReal e) (fun _ => id)
        (if kind then sign r else hash r) tbl)
      return (⟨(), fun | .g₁ => [(st.handles .g₁).length] | .g₂ => [] | .gₜ => []⟩,
        reductionReceive st kind m h, tbl')

private theorem combinedHandler_eq [CommSemiring F] [DecidableEq F]
    [∀ b, AddCommMonoid (G b)] [∀ b, Module F (G b)]
    [AddCommMonoid T] [Module F T]
    [∀ s, DecidableEq (PFam (G false) (G true) T s)]
    (e : G false →ₗ[F] G true →ₗ[F] T) (z : PSort → Handle)
    (hash sign : R → OracleComp (genSpec F pairingSig) Handle) :
    combinedHandler (M := M) e z hash sign =
      ((openImpl (M := M) (R := R) (pairingReal e) (fun _ => id)).mapStateTBase
        (reductionHandler z hash sign)).flattenStateT := by
  funext q st
  rcases st with ⟨st, tbl⟩
  change (combinedHandler e z hash sign q).run (st, tbl) =
    (((openImpl (M := M) (R := R) (pairingReal e) (fun _ => id)).mapStateTBase
      (reductionHandler z hash sign)).flattenStateT q).run (st, tbl)
  rw [QueryImpl.flattenStateT_mapStateTBase_apply_run]
  rcases q with q | q | n | q
  · simp only [combinedHandler, reductionHandler, StateT.run, bind_pure_comp]
    change _ = _ <$> (simulateQ (openImpl (M := M) (R := R)
      (pairingReal e) (fun _ => id)) _).run tbl
    simp only [simulateQ_map, StateT.run_map, openImpl_reductionLift, Functor.map_map]
  · rfl
  · simp only [combinedHandler, reductionHandler, StateT.run]
    rfl
  · rcases q with ⟨m | m, gs⟩ <;>
      simp only [combinedHandler, reductionHandler, StateT.run, bind_pure_comp,
        Bool.false_eq_true, ite_false, ite_true]
    all_goals
      change _ = _ <$> (simulateQ (openImpl (M := M) (R := R)
        (pairingReal e) (fun _ => id)) _).run tbl
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
      simp only [openImpl, QueryImpl.add_apply_inr, QueryImpl.liftTarget_apply,
        QueryImpl.ofLift_apply, liftM_run_StateT, bind_assoc, pure_bind]
      apply bind_congr
      intro r
      change _ = _ <$> (simulateQ (openImpl (M := M) (R := R)
        (pairingReal e) (fun _ => id)) _).run tbl
      simp only [simulateQ_map, StateT.run_map, openImpl_reductionLift, Functor.map_map]
      rfl

private theorem combinedHandler_run_view [CommSemiring F] [DecidableEq F]
    [∀ b, AddCommMonoid (G b)] [∀ b, Module F (G b)] [∀ b, DecidableEq (G b)]
    [AddCommMonoid T] [Module F T] [DecidableEq T]
    [∀ s, DecidableEq (PFam (G false) (G true) T s)]
    (e : G false →ₗ[F] G true →ₗ[F] T) (z : PSort → Handle)
    (hash sign : R → OracleComp (genSpec F pairingSig) Handle)
    (hashValue signValue : R → G false)
    (root : Tbl (PFam (G false) (G true) T))
    (hhash : RealizesPoint e root hash hashValue) (hsign : RealizesPoint e root sign signValue)
    (program : OracleComp (adversarySpec F M) (Message M (fun _ : PSort => Handle)))
    (st : ReductionState F M) (tbl : Tbl (PFam (G false) (G true) T))
    (real : RealReductionState F M G T) (h : ReductionRelated root z st tbl real) :
    (fun a => reductionView a.1 a.2.1) <$>
      (simulateQ (combinedHandler e z hash sign) program).run (st, tbl) =
    (fun a => realReductionView a.1 a.2) <$>
      (simulateQ (realReductionHandler e hashValue signValue) program).run real := by
  induction program using OracleComp.inductionOn generalizing st tbl real with
  | pure out =>
      simpa only [simulateQ_pure, StateT.run_pure, map_pure] using
        congrArg pure (h.view_eq out)
  | query_bind q next ih =>
      simp only [run_simulateQ_query_bind, map_bind]
      rcases q with q | q | n | q
      · obtain ⟨r, hr⟩ := exists_runGen_virtualize_group (pairingReal e) (fun _ => id)
          z q st.handles tbl
        obtain ⟨he, h'⟩ := h.group e q r hr
        simp only [StateT.run] at hr
        simp only [combinedHandler, realReductionHandler, StateT.run, hr,
          liftM_pure, pure_bind]
        exact (ih r.1.1 _ _ _ h').trans (by rw [he]; rfl)
      · simpa only [combinedHandler, realReductionHandler, StateT.run, pure_bind] using
          ih () st tbl real h
      · simp only [combinedHandler, realReductionHandler, StateT.run, bind_assoc, pure_bind]
        apply bind_congr
        intro coin
        exact ih coin st tbl real h
      · rcases q with ⟨m | m, gs⟩ <;>
          simp only [combinedHandler, realReductionHandler, StateT.run, bind_assoc,
            pure_bind, Bool.false_eq_true, ite_false, ite_true]
        · apply bind_congr
          intro r
          obtain ⟨handle, tbl', hr, hp, hh, hv⟩ := hhash r tbl h.extendsRoot
          simp only [hr, liftM_pure, pure_bind]
          have h' := ih ⟨(), fun | .g₁ => [(st.handles .g₁).length] | .g₂ => [] | .gₜ => []⟩
            _ _ _ (h.receive hp handle hh false m (hashValue r) hv)
          simpa only [h.source_length, StateT.run] using h'
        · apply bind_congr
          intro r
          obtain ⟨handle, tbl', hr, hp, hh, hv⟩ := hsign r tbl h.extendsRoot
          simp only [hr, liftM_pure, pure_bind]
          have h' := ih ⟨(), fun | .g₁ => [(st.handles .g₁).length] | .g₂ => [] | .gₜ => []⟩
            _ _ _ (h.receive hp handle hh true m (signValue r) hv)
          simpa only [h.source_length, StateT.run] using h'

/-- Real interpretation of the virtual reduction preserves every scalar-extraction input. -/
theorem run_reductionHandler_view [CommSemiring F] [DecidableEq F]
    [∀ b, AddCommMonoid (G b)] [∀ b, Module F (G b)] [∀ b, DecidableEq (G b)]
    [AddCommMonoid T] [Module F T] [DecidableEq T]
    [∀ s, DecidableEq (PFam (G false) (G true) T s)]
    (e : G false →ₗ[F] G true →ₗ[F] T) (z : PSort → Handle)
    (hash sign : R → OracleComp (genSpec F pairingSig) Handle)
    (hashValue signValue : R → G false)
    (root : Tbl (PFam (G false) (G true) T))
    (hhash : RealizesPoint e root hash hashValue) (hsign : RealizesPoint e root sign signValue)
    (program : OracleComp (adversarySpec F M) (Message M (fun _ : PSort => Handle)))
    (st : ReductionState F M) (tbl : Tbl (PFam (G false) (G true) T))
    (real : RealReductionState F M G T) (h : ReductionRelated root z st tbl real) :
    (fun a => reductionView a.1.1 a.1.2) <$>
      (simulateQ (openImpl (pairingReal e) (fun _ => id))
        ((simulateQ (reductionHandler z hash sign) program).run st)).run tbl =
    (fun a => realReductionView a.1 a.2) <$>
      (simulateQ (realReductionHandler e hashValue signValue) program).run real := by
  rw [simulateQ_mapStateTBase_run_eq_map_flattenStateT, ← combinedHandler_eq]
  simpa only [Functor.map_map] using
    combinedHandler_run_view e z hash sign hashValue signValue root hhash hsign
      program st tbl real h

end BLS.Generic
