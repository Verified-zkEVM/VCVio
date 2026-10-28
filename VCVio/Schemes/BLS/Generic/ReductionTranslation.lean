/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.Schemes.BLS.Generic.ReductionExecution
public import VCVio.Schemes.BLS.Generic.Translation
public import VCVio.Schemes.BLS.AGM.Reductions
import all VCVio.Schemes.BLS.AGM.Adversary
import all VCVio.Schemes.BLS.AGM.Reductions
import all VCVio.Schemes.BLS.Generic.Translation
import all VCVio.Schemes.BLS.Generic.Adversary
import all VCVio.CryptoFoundations.GroupModel.Instances

/-! # Chronological execution of the certified BLS translation

The real extraction view of the generic reduction agrees with the coefficient list and reply
transcript consumed by the algebraic reductions.
-/

public section

open OracleComp OracleSpec GroupModel GroupModel.Interaction

namespace BLS.Generic

variable {F M R G₁ G₂ Gₜ : Type}

attribute [local implicit_reducible] spec handleSpec encSpec AGM.Reply CoinReply Sum.elim

/-- Executing the certified translation retains precisely the real scalar-extraction view. -/
theorem explainProgram_transcript_view [Field F]
    [AddCommGroup G₁] [Module F G₁] [DecidableEq G₁]
    [AddCommGroup G₂] [Module F G₂] [DecidableEq G₂]
    [AddCommGroup Gₜ] [Module F Gₜ] [DecidableEq Gₜ]
    (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (hash sign : R → G₁)
    (program : OracleComp (adversarySpec F M) (Message M (fun _ : PSort => Handle)))
    (st : Pairing.Tracked F (AGM.Group G₁ G₂) Gₜ) (tr : LinearFunctional.Transcript M) :
    (fun a => (a.1.value.data,
      (if (a.1.value.groups false).isEmpty then []
        else (a.1.coefficients false).headD []), a.2)) <$>
      (simulateQ (LinearFunctional.transcriptOracle hash sign)
        (simulateQ (fun q => AGM.oracle q.value)
          (simulateQ relabel
            (Pairing.explainProgram (G := AGM.Group G₁ G₂) e program st)))).run tr =
    (fun a => realReductionView a.1 a.2) <$>
      (simulateQ (realReductionHandler (G := AGM.Group G₁ G₂) e hash sign) program).run
        (st, tr) := by
  have hgroups (v : G₁) : AGM.groupInputs [v] ([] : List G₂) =
      fun | false => [v] | true => [] := by
    funext b
    cases b <;> rfl
  rw [relabel_run]
  induction program using OracleComp.inductionOn generalizing st tr with
  | pure out =>
      simp only [Pairing.explainProgram_pure, simulateQ_pure, StateT.run_pure, map_pure]
      congr 1
      cases ho : out.groups .g₁ <;>
        simp [realReductionView, explain, Pairing.sourceMessage, ho]
  | query_bind q next ih =>
      rw [run_simulateQ_query_bind]
      simp only [map_bind]
      rcases q with q | q | n | q
      · simpa only [Pairing.explainProgram_query_bind, realReductionHandler,
          StateT.run, pure_bind] using ih (Pairing.step e q st).1 (Pairing.step e q st).2 tr
      · simpa only [Pairing.explainProgram_query_bind, realReductionHandler,
          StateT.run, pure_bind] using ih () st tr
      · have hcoin : simulateQ (LinearFunctional.transcriptOracle hash sign)
            (liftM (unifSpec.query n) : OracleComp (AGM.rawSpec M G₁) _) =
            LinearFunctional.transcriptOracle hash sign (.inl (.inl n)) := by
          change simulateQ _ (liftM ((AGM.rawSpec M G₁).query (.inl (.inl n)))) = _
          exact simulateQ_spec_query _ _
        simp only [Pairing.explainProgram_query_bind, simulateQ_bind, simulateQ_spec_query,
          withCoins_apply_inr, QueryImpl.ofLift_apply, hcoin,
          simulateQ_pure,
          StateT.run_bind, StateT.run_pure,
          map_bind]
        simp only [realReductionHandler, StateT.run, bind_assoc, pure_bind,
          LinearFunctional.transcriptOracle, bind_map_left, receive_empty]
        apply bind_congr
        intro coin
        simpa only [StateT.run] using ih coin st tr
      · rcases q with ⟨m | m, gs⟩ <;>
          simp only [Pairing.explainProgram_query_bind, explain, Pairing.sourceMessage,
            simulateQ_bind, simulateQ_spec_query, withCoins_apply_inl, sourceOracle,
            bind_assoc, pure_bind,
            StateT.run_bind,
            LinearFunctional.transcriptOracle_hash, LinearFunctional.transcriptOracle_sign,
            map_bind]
        all_goals
          simp only [realReductionHandler, StateT.run, bind_assoc, pure_bind,
            Bool.false_eq_true, ite_false, ite_true, OracleComp.liftM_map, bind_map_left]
          apply bind_congr
          intro r
        · simp only [hgroups, List.length_cons, List.length_nil, List.range'_zero]
          convert ih ⟨(), fun | .g₁ => [(st.1.2 false).length] | .g₂ => [] | .gₜ => []⟩
              (receive st.1 (fun | false => [hash r] | true => []), st.2) (tr ++ [(false, m)])
            using 1 <;> rfl
        · simp only [hgroups, List.length_cons, List.length_nil, List.range'_zero]
          convert ih ⟨(), fun | .g₁ => [(st.1.2 false).length] | .g₂ => [] | .gₜ => []⟩
              (receive st.1 (fun | false => [sign r] | true => []), st.2) (tr ++ [(true, m)])
            using 1 <;> rfl

end BLS.Generic
