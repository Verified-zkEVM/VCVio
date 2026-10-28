/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.Schemes.BLS.Generic.Adversary
public import VCVio.CryptoFoundations.GroupModel.PairingExplained
import all VCVio.Schemes.BLS.AGM.Adversary
import all VCVio.Schemes.BLS.Generic.Adversary
import all VCVio.CryptoFoundations.GroupModel.Instances

/-! # Certified source explanations of generic BLS adversaries

Private coins, hashes and signing requests are forwarded to the algebraic BLS interface.
The certificate explains only source elements; target values are internal to the pairing
interpreter. The protocol certificate enforces group-free requests and one output signature.
-/

public section

open OracleComp OracleSpec GroupModel GroupModel.Interaction

namespace BLS.Generic

variable {F M G₁ G₂ Gₜ : Type}

/-- Reassociate the three query kinds into the algebraic BLS interface. -/
@[expose] def relabel :
    QueryImpl (explainedSpec F (AGM.Group G₁ G₂) (CoinQuery (Query M))
      (CoinReply (fun _ => Unit)))
      (OracleComp (explainedSpec F (AGM.Group G₁ G₂) (AGM.Query M) AGM.Reply))
  | ⟨⟨.inl (.inl m), gs⟩, cs⟩ =>
      (explainedSpec F (AGM.Group G₁ G₂) (AGM.Query M) AGM.Reply).query
        ⟨⟨.inl (.inr m), gs⟩, cs⟩
  | ⟨⟨.inl (.inr m), gs⟩, cs⟩ =>
      (explainedSpec F (AGM.Group G₁ G₂) (AGM.Query M) AGM.Reply).query
        ⟨⟨.inr m, gs⟩, cs⟩
  | ⟨⟨.inr n, gs⟩, cs⟩ =>
      (explainedSpec F (AGM.Group G₁ G₂) (AGM.Query M) AGM.Reply).query
        ⟨⟨.inl (.inl n), gs⟩, cs⟩

private theorem relabel_isAlgebraic [Zero F]
    [AddMonoid G₁] [SMul F G₁] [AddMonoid G₂] [SMul F G₂]
    (p : OracleComp (explainedSpec F (AGM.Group G₁ G₂) (CoinQuery (Query M))
      (CoinReply (fun _ => Unit))) (Explained F M (AGM.Group G₁ G₂)))
    (gs : Groups (AGM.Group G₁ G₂)) (hp : IsAlgebraic gs p) :
    IsAlgebraic gs (simulateQ relabel p) := by
  induction p using OracleComp.inductionOn generalizing gs with
  | pure out => simpa using hp
  | query_bind q next ih =>
      rcases q with ⟨⟨(m | m) | n, qs⟩, cs⟩ <;>
        simp only [simulateQ_bind, simulateQ_spec_query, relabel] <;>
        exact ⟨hp.1, fun reply => ih reply _ (hp.2 reply)⟩

private theorem explainProgram_protocol [CommSemiring F]
    [AddCommGroup G₁] [Module F G₁] [DecidableEq G₁]
    [AddCommGroup G₂] [Module F G₂] [DecidableEq G₂]
    [AddCommMonoid Gₜ] [Module F Gₜ] [DecidableEq Gₜ]
    (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ)
    (p : OracleComp (adversarySpec F M) (Message M (fun _ : PSort => Handle)))
    (st : Pairing.Tracked F (AGM.Group G₁ G₂) Gₜ)
    (hp : allPathsSatisfy
      (fun q => match q with
        | .inr (.inr (.inr q)) => ∀ s, q.groups s = []
        | _ => True)
      (fun out => (out.groups .g₁).length = 1 ∧ out.groups .g₂ = [] ∧ out.groups .gₜ = [])
      (fun _ => Set.univ) p) :
    allPathsSatisfy (fun q => ∀ s, q.value.groups s = [])
      (fun out => (out.value.groups false).length = 1 ∧ out.value.groups true = [])
      (fun _ => Set.univ)
      (simulateQ relabel (Pairing.explainProgram (G := AGM.Group G₁ G₂) e p st)) := by
  induction p using OracleComp.inductionOn generalizing st with
  | pure out =>
      simp only [allPathsSatisfy_pure] at hp
      change allPathsSatisfy _ _ _
        (simulateQ relabel (pure (explain st.1 (Pairing.sourceMessage out))))
      simp only [simulateQ_pure, allPathsSatisfy_pure]
      constructor
      · simpa [explain, Pairing.sourceMessage] using hp.1
      · simp [explain, Pairing.sourceMessage, hp.2.1]
  | query_bind q next ih =>
      obtain ⟨hq, hn⟩ := allPathsSatisfy_query_bind _ _ |>.mp hp
      rcases q with q | q | n | q
      · exact ih _ _ (hn _ (Set.mem_univ _))
      · exact ih () st (hn () (Set.mem_univ _))
      · change allPathsSatisfy _ _ _ (simulateQ relabel (liftM
          ((explainedSpec F (AGM.Group G₁ G₂) (CoinQuery (Query M))
            (CoinReply (fun _ => Unit))).query
            ⟨⟨.inr n, fun _ => []⟩, fun _ => []⟩) >>= _))
        simp only [simulateQ_bind, simulateQ_spec_query, relabel]
        apply (allPathsSatisfy_query_bind _ _).mpr
        exact ⟨fun _ => rfl, fun reply _ => ih _ _ (hn _ (Set.mem_univ _))⟩
      · rcases q with ⟨m | m, qs⟩ <;>
          have hqs : ∀ s, qs s = [] := hq <;>
          simp only [Pairing.explainProgram, explain, Pairing.sourceMessage] <;>
          apply (allPathsSatisfy_query_bind _ _).mpr <;>
          refine ⟨?_, fun reply _ => ih _ _ (hn _ (Set.mem_univ _))⟩ <;>
          intro b <;> cases b <;>
          simp only [hqs, List.map_nil]

/-- Translate a protocol-respecting generic BLS adversary into a certified algebraic adversary. -/
@[expose] def Adversary.toAlgebraic [Field F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ] [DecidableEq Gₜ]
    [DecidableEq G₁] [DecidableEq G₂]
    (A : Adversary F M) (hA : FollowsProtocol A)
    (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₁ : G₁) (g₂ : G₂) :
    AlgebraicAdversary F M G₁ G₂ e g₁ g₂ where
  main input := simulateQ relabel ((Pairing.toExplained (G := AGM.Group G₁ G₂) e A).main input)
  algebraic input := by
    exact relabel_isAlgebraic _ _
      ((Pairing.toExplained (G := AGM.Group G₁ G₂) e A).algebraic input)
  protocol input := by exact explainProgram_protocol e _ _ (hA _)

private def sourceOracle :
    QueryImpl (plainSpec (AGM.Group G₁ G₂) (Query M) (fun _ => Unit))
      (OracleComp (AGM.rawSpec M G₁))
  | ⟨.inl m, _⟩ => do
      let h ← (AGM.rawSpec M G₁).query (.inl (.inr m))
      return ⟨(), AGM.groupInputs [h] []⟩
  | ⟨.inr m, _⟩ => do
      let h ← (AGM.rawSpec M G₁).query (.inr m)
      return ⟨(), AGM.groupInputs [h] []⟩

attribute [local implicit_reducible] AGM.Reply CoinReply GroupModel.PFam

private theorem relabel_run
    (p : OracleComp (explainedSpec F (AGM.Group G₁ G₂) (CoinQuery (Query M))
      (CoinReply (fun _ => Unit))) (Explained F M (AGM.Group G₁ G₂))) :
    simulateQ (fun q => AGM.oracle q.value) (simulateQ relabel p) =
      simulateQ (fun q => withCoins
        (QueryImpl.ofLift unifSpec (OracleComp (AGM.rawSpec M G₁))) sourceOracle q.value) p := by
  apply QueryImpl.simulateQ_simulateQ_eq_of_apply
  rintro ⟨⟨(m | m) | n, gs⟩, cs⟩
  · exact simulateQ_spec_query
      (spec := explainedSpec F (AGM.Group G₁ G₂) (AGM.Query M) AGM.Reply)
      (fun q => AGM.oracle q.value)
      (⟨⟨.inl (.inr m), gs⟩, cs⟩ : Explained F (AGM.Query M) (AGM.Group G₁ G₂))
  · exact simulateQ_spec_query
      (spec := explainedSpec F (AGM.Group G₁ G₂) (AGM.Query M) AGM.Reply)
      (fun q => AGM.oracle q.value)
      (⟨⟨.inr m, gs⟩, cs⟩ : Explained F (AGM.Query M) (AGM.Group G₁ G₂))
  · have h := simulateQ_spec_query
      (spec := explainedSpec F (AGM.Group G₁ G₂) (AGM.Query M) AGM.Reply)
      (fun q => AGM.oracle (G₁ := G₁) (G₂ := G₂) q.value)
      (⟨⟨.inl (.inl n), gs⟩, cs⟩ : Explained F (AGM.Query M) (AGM.Group G₁ G₂))
    have he : AGM.groupInputs ([] : List G₁) ([] : List G₂) = fun _ => [] := by
      funext b
      cases b <;> rfl
    refine h.trans ?_
    change (do
      let a ← (liftM ((AGM.rawSpec M G₁).query (.inl (.inl n))) :
        OracleComp (AGM.rawSpec M G₁) (Fin (n + 1)))
      pure (⟨a, AGM.groupInputs [] []⟩ : Message (Fin (n + 1)) (AGM.Group G₁ G₂))) = _
    rw [he]
    rfl

private theorem game_sourceOracle :
    Pairing.game (T := Gₜ) (sourceOracle (M := M) (G₁ := G₁) (G₂ := G₂)) = oracle := by
  funext q
  rcases q with ⟨m | m, gs⟩ <;>
    simp [Pairing.game, sourceOracle, Pairing.sourceValue, Pairing.pairingMessage,
      oracle, AGM.groupInputs] <;> rfl

/-- Forgetting the certified translation gives the ordinary real interpretation of the
same generic BLS adversary, as an exact equality of adversary programs. -/
theorem Adversary.toAlgebraic_toUnforgeableAdversary [Field F] [SampleableType F]
    [AddCommGroup G₁] [Module F G₁] [DecidableEq G₁]
    [AddCommGroup G₂] [Module F G₂] [DecidableEq G₂]
    [AddCommGroup Gₜ] [Module F Gₜ] [DecidableEq Gₜ]
    [∀ s, DecidableEq (PFam G₁ G₂ Gₜ s)]
    (A : Adversary F M) (hA : FollowsProtocol A)
    (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₁ : G₁) (g₂ : G₂) :
    (A.toAlgebraic hA e g₁ g₂).toUnforgeableAdversary =
      A.toUnforgeableAdversary e g₁ g₂ := by
  change SignatureAlg.UnforgeableAdversary.mk _ = SignatureAlg.UnforgeableAdversary.mk _
  congr 1
  funext pk
  have h := Pairing.toExplained_run (G := AGM.Group G₁ G₂) e A
    (QueryImpl.ofLift unifSpec (OracleComp (AGM.rawSpec M G₁))) sourceOracle
    (AGM.initialInput g₁ g₂ pk)
  unfold Interaction.Adversary.run at h
  rw [run_value, game_sourceOracle] at h
  have hd := congrArg (fun p =>
    (fun out : Message M (AGM.Group G₁ G₂) =>
      (out.data, (out.groups false).headD 0)) <$> p) h
  simp only [Adversary.toAlgebraic, relabel_run, Functor.map_map,
    Pairing.sourceValue, Pairing.pairingMessage,
    AGM.initialInput, AGM.groupInputs, initialInput] at hd ⊢
  convert hd using 1 <;> rfl

end BLS.Generic
