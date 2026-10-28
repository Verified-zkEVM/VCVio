/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Schemes.Schnorr.AGM.Simulation
import all VCVio.Schemes.Schnorr.AGM.Simulation
import all VCVio.Schemes.Schnorr.AGM.Soundness
import all VCVio.CryptoFoundations.FiatShamir.Sigma.Stateful.Chain.Simulation

/-! # Erasing Schnorr extraction metadata

The annotated first-explanation cache projects to the existing Fiat-Shamir simulator's
scalar cache. Signing history is preserved in chronological order.
-/

public section

open OracleComp OracleSpec GroupModel.Interaction
open FiatShamir FiatShamir.Stateful

namespace Schnorr.AGM

variable {F G M : Type}

private def cacheProjection [Field F] (s : Reduction.State F G M) :
    (fsRoSpec M G F).QueryCache :=
  QueryCache.ofFn fun t => match t with
    | .inl _ => none
    | .inr key => (s.cache key).map Reduction.Entry.challenge

private def stateProjection [Field F] (s : Reduction.State F G M) :
    (fsRoSpec M G F).QueryCache × List M := (cacheProjection s, s.signed)

private theorem cacheProjection_record [Field F] [DecidableEq F]
    [DecidableEq G] [DecidableEq M] (s : Reduction.State F G M) (key : M × G)
    (a : GroupModel.LinearFunctional.AffineForm F) (c : F) :
    cacheProjection (Reduction.record s key a c) =
      (cacheProjection s).cacheQuery (.inr key) c := by
  ext t
  cases t with
  | inl n => simp [cacheProjection, Reduction.record]
  | inr k =>
      by_cases h : k = key
      · subst k; simp [cacheProjection, Reduction.record]
      · simp [cacheProjection, Reduction.record, h]

private theorem erased_handler_step [Field F] [SampleableType F]
    [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] [DecidableEq M]
    (g pk : G) (s : Reduction.State F G M)
    (q : Explained F (Request M) (Group G)) (hshape : RequestShape q)
    (hvalid : q.Valid (representedBasis g pk s.representations)) :
    Prod.map id stateProjection <$> (Reduction.handler g pk q).run s =
      (simulateQ (simulatedNmaLoggedProbImpl (M := M) (Commit := G) (Chal := F)
        (Resp := F) (Schnorr.simTranscript F G g) pk) (oracle q.value)).run
        (stateProjection s) := by
  rcases q with ⟨⟨request, groups⟩, coeffs⟩
  cases request with
  | random n =>
      change groups () = [] at hshape
      conv_lhs => dsimp only [Reduction.handler, StateT.run]
      simp [ hshape, oracle, simulatedNmaLoggedProbImpl,
        QueryImpl.mapStateTBase, simulatedNmaImpl, simulatedNmaBaseSim,
        simulatedNmaUnifSim, simulatedNmaFwd, fsUniformImpl,
        cmaOracleSignLogAux, stateProjection]
  | hash m =>
      change (groups ()).length = 1 at hshape
      obtain ⟨R, hR⟩ := List.length_eq_one_iff.mp hshape
      obtain ⟨coeff, hcoeff, _, _⟩ := valid_singleton g pk R s.representations
        ⟨⟨Request.hash m, groups⟩, coeffs⟩ hvalid hR
      change coeffs () = [coeff] at hcoeff
      conv_lhs => dsimp only [Reduction.handler, StateT.run]
      simp only [hR, hcoeff, Reduction.read, bind_pure_comp, Functor.map_map, Prod.map_apply,
        id_eq, stateProjection, simulatedNmaLoggedProbImpl, fsUniformImpl,
        QueryImpl.ofLift_eq_id', simulatedNmaImpl, simulatedNmaBaseSim, oracle, add_apply_inl,
        add_apply_inr, simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, simulateQ_pure, StateT.run_bind,
        QueryImpl.extendState_apply, QueryImpl.mapStateTBase, QueryImpl.add_apply_inl,
        QueryImpl.add_apply_inr, simulatedNmaRoSim, simulatedNmaFwd,
        PFunctor.Handler.liftTarget_apply, ofPFunctor_toPFunctor, QueryImpl.id'_apply,
        StateT.run_get, pure_bind, StateT.run_mk, cmaOracleSignLogAux, StateT.run_pure]
      have hhead : (groups ()).headD 0 = R := by rw [hR]; rfl
      dsimp only [explainedSpec, plainSpec, Reply]
      erw [hhead]
      cases hc : s.cache (m, R) with
      | some e => simp [hc, cacheProjection]
      | none =>
          simp only [cacheProjection, Functor.map_map, QueryCache.ofFn_apply, hc,
            Option.map_none, StateT.run_bind, StateT.run_monadLift, monadLift_self,
            bind_pure_comp, StateT.run_modifyGet, simulateQ_map, simulateQ_query,
            OracleQuery.input_query, OracleQuery.cont_query, QueryImpl.add_apply_inr,
            uniformSampleImpl_apply, id_map]
          congr 1
          funext c
          congr 1
          exact Prod.ext (cacheProjection_record s (m, R) _ c) rfl
  | sign m =>
      change groups () = [] at hshape
      conv_lhs => dsimp only [Reduction.handler, StateT.run]
      simp only [hshape, ne_eq, not_true_eq_false, ite_false, bind_pure_comp, map_bind,
        Functor.map_map, Prod.map_apply, id_eq, stateProjection, simulatedNmaLoggedProbImpl,
        simulatedNmaImpl, oracle, add_apply_inr, simulateQ_map, simulateQ_query,
        OracleQuery.input_query, OracleQuery.cont_query, id_map, StateT.run_map,
        QueryImpl.extendState_apply, QueryImpl.mapStateTBase, QueryImpl.add_apply_inr,
        simulatedNmaSigSim, Schnorr.simTranscript, simulateQ_bind, bind_assoc, bind_map_left,
        StateT.run_bind, StateT.run_modifyGet, Prod.mk.eta, simulatedNmaUnifSim_fsUniform_run,
        StateT.run_mk, cmaOracleSignLogAux]
      apply bind_congr
      intro c
      congr 1
      funext z
      cases hc : s.cache (m, z • g - c • pk) <;>
        simp only [cacheProjection, Reduction.signedState, Reduction.programEntry_eq,
          hc, QueryCache.ofFn_apply, Option.map_none, Option.map_some, Prod.mk.injEq,
          and_true, true_and]
      congr 1
      ext t
      cases t with
      | inl n => simp
      | inr k =>
          by_cases h : k = (m, z • g - c • pk)
          · subst k; simp
          · simp [h]

private theorem handler_malformed [Field F] [SampleableType F]
    [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] [DecidableEq M]
    (g pk : G) (s : Reduction.State F G M)
    (q : Explained F (Request M) (Group G)) (hshape : RequestShape q)
    (hvalid : q.Valid (representedBasis g pk s.representations))
    (reply : Message (Reply F M q.value.data) (Group G)) (t : Reduction.State F G M)
    (h : (reply, t) ∈ support ((Reduction.handler g pk q).run s)) :
    t.malformed = s.malformed := by
  rcases q with ⟨⟨request, groups⟩, coeffs⟩
  cases request with
  | random n =>
      change groups () = [] at hshape
      simp only [Reduction.handler, StateT.run, hshape, ite_true,
        mem_support_bind_iff, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h
      obtain ⟨v, _, _, rfl⟩ := h
      rfl
  | sign m =>
      change groups () = [] at hshape
      simp only [Reduction.handler, StateT.run, hshape, ne_eq, not_true_eq_false,
        ite_false, mem_support_bind_iff] at h
      obtain ⟨c, _, z, _, h⟩ := h
      simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      rfl
  | hash m =>
      change (groups ()).length = 1 at hshape
      obtain ⟨R, hR⟩ := List.length_eq_one_iff.mp hshape
      obtain ⟨coeff, hcoeff, _, _⟩ := valid_singleton g pk R s.representations
        ⟨⟨Request.hash m, groups⟩, coeffs⟩ hvalid hR
      change coeffs () = [coeff] at hcoeff
      simp only [Reduction.handler, StateT.run, hR, hcoeff, mem_support_bind_iff] at h
      obtain ⟨⟨c, st⟩, hc, h⟩ := h
      simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      cases he : s.cache (m, R) <;>
        simp only [Reduction.read, he, mem_support_bind_iff,
          support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hc
      · obtain ⟨d, _, rfl, rfl⟩ := hc
        rfl
      · obtain ⟨rfl, rfl⟩ := hc
        rfl

private theorem finish_projection [Field F] [SampleableType F] [SampleableType G]
    [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] [DecidableEq M]
    (g pk : G) (s : Reduction.State F G M) (hs : s.malformed = false)
    (out : Explained F (M × F) (Group G)) (hshape : (out.value.groups ()).length = 1)
    (hvalid : out.Valid (representedBasis g pk s.representations)) :
    (fun p => p.1.1) <$> (Reduction.finish g pk out).run s =
      simLoggedVerifyFreshComp (M := M) (Schnorr.sigma F G g) pk
        (forgery out) (stateProjection s) := by
  obtain ⟨R, hR⟩ := List.length_eq_one_iff.mp hshape
  obtain ⟨coeff, hcoeff, _, _⟩ := valid_singleton g pk R s.representations out hvalid hR
  simp only [Reduction.finish, hR, hcoeff]
  cases hc : s.cache (out.value.data.1, R) <;>
    simp only [Bool.decide_and, decide_not, bind_pure_comp, StateT.run_bind, StateT.run_get,
      StateT.run_map, map_pure, pure_bind, Functor.map_map, simLoggedVerifyFreshComp,
      stateProjection, cacheProjection, forgery, QueryCache.ofFn_apply, hR,
      List.headD_eq_head?_getD, List.head?_cons, Option.getD_some, hc, Option.map_none,
      Option.map_some, Schnorr.sigma] <;>
    simp [Reduction.read, StateT.run, hc, Reduction.record, hs, Functor.map_map]

private theorem erased_program [Field F] [SampleableType F] [SampleableType G]
    [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] [DecidableEq M]
    (g pk : G)
    (program : OracleComp (explainedSpec F (Group G) (Request M) (Reply F M))
      (Explained F (M × F) (Group G)))
    (s : Reduction.State F G M) (hs : s.Valid g pk) (hm : s.malformed = false)
    (halg : IsAlgebraic (representedBasis g pk s.representations) program)
    (hshape : allPathsSatisfy RequestShape (fun out => (out.value.groups ()).length = 1)
      (fun _ => Set.univ) program) :
    (fun p => p.1.1) <$>
        (simulateQ (Reduction.handler g pk) program >>= Reduction.finish g pk).run s = (do
      let p ← (simulateQ
        (simulatedNmaLoggedProbImpl (M := M) (Commit := G) (Chal := F)
          (Resp := F) (Schnorr.simTranscript F G g) pk)
        (simulateQ (fun q => oracle q.value) program)).run (stateProjection s)
      simLoggedVerifyFreshComp (M := M) (Schnorr.sigma F G g) pk (forgery p.1) p.2) := by
  induction program using OracleComp.inductionOn generalizing s with
  | pure out =>
      simp only [simulateQ_pure, pure_bind, StateT.run_pure]
      exact finish_projection g pk s hm out (by simpa using hshape) halg
  | query_bind q next ih =>
      obtain ⟨hq, hn⟩ := (isAlgebraic_query _ _ _).mp halg
      obtain ⟨hqs, hns⟩ := (allPathsSatisfy_query_bind q next).mp hshape
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind, bind_assoc]
      rw [← erased_handler_step g pk s q hqs hq, bind_map_left]
      apply bind_congr_of_forall_mem_support
      rintro ⟨reply, st⟩ hr
      have hv := Reduction.handler_spec g pk s hs q hq reply st hr
      have hm' := (handler_malformed g pk s q hqs hq reply st hr).trans hm
      simpa only [StateT.run_bind, map_bind, Prod.map_apply, id_eq] using ih reply st hv.1 hm'
        (by rw [hv.2]; exact hn reply) (hns reply (Set.mem_univ _))

/-- The certified algebraic run, after forgetting extraction state, is the existing
freshness-preserving Fiat-Shamir signing simulation. -/
theorem simulatedCma_eq_run [Field F] [SampleableType F] [SampleableType G]
    [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] [DecidableEq M]
    (g : G) (A : Schnorr.AlgebraicAdversary F G M) :
    (cmaSim M G F (DiffieHellman.dlogGenerable F g) (Schnorr.simTranscript F G g)).runProb
      (cmaInit M G F G F)
      (signedFreshAdv (Schnorr.sigma F G g) (DiffieHellman.dlogGenerable F g) M
        (A.toUnforgeableAdversary g)) = (do
      let x ← $ᵗ F
      (fun p => p.1.1) <$> Reduction.run g (x • g) A) := by
  rw [simulatedCma_eq_normalForm]
  apply bind_congr
  intro x
  have he := erased_program g (x • g) (A.main (initial g (x • g))) {}
    (Reduction.initial_valid g (x • g)) rfl
    (by simpa using A.algebraic (initial g (x • g))) (A.protocol _)
  have hempty : stateProjection ({} : Reduction.State F G M) = (∅, []) := by
    dsimp only [stateProjection]
    congr 1
    ext t
    cases t <;> rfl
  rw [hempty] at he
  simpa [AlgebraicAdversary.toUnforgeableAdversary, simulateQ_map, Reduction.run] using he.symm

end Schnorr.AGM
