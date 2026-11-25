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
interpreter. Every generic adversary translates: the algebraic BLS interface places no
restriction on the shape of requests or outputs.
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

/-- Translate a generic BLS adversary into a certified algebraic adversary. -/
@[expose] def Adversary.toAlgebraic [Field F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ] [DecidableEq Gₜ]
    [DecidableEq G₁] [DecidableEq G₂]
    (A : Adversary F M)
    (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₁ : G₁) (g₂ : G₂) :
    AlgebraicAdversary F M G₁ G₂ e g₁ g₂ where
  main input := simulateQ relabel ((Pairing.toExplained (G := AGM.Group G₁ G₂) e A).main input)
  algebraic input := by
    exact relabel_isAlgebraic _ _
      ((Pairing.toExplained (G := AGM.Group G₁ G₂) e A).algebraic input)

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
    (A : Adversary F M)
    (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₁ : G₁) (g₂ : G₂) :
    (A.toAlgebraic e g₁ g₂).toUnforgeableAdversary =
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
