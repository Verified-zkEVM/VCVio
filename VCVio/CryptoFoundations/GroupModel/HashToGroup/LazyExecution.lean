/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.GroupModel.HashToGroup.SlotTransport

/-! # Coin-bearing interactions over a lazily sampled hash oracle

The raw oracle interface separates private uniform draws from hash labels. Its finite-table
execution retains the chronological receipt log used by certified interaction explanations.
-/

public section

namespace GroupModel.HashToGroup

open OracleComp OracleSpec Interaction

variable {Label F G α σ : Type} {n q : ℕ}

/-- Present ordinary hash and private-coin queries as interaction replies. Hashes return one
group input; private coins return only plain data. -/
@[expose] def rawGame :
    QueryImpl (plainSpec (fun _ : Unit => G) (CoinQuery Label) (CoinReply (fun _ => Unit)))
      (OracleComp (unifSpec + (Label →ₒ G)))
  | ⟨.inl l, _⟩ => reply <$> (liftM ((unifSpec + (Label →ₒ G)).query (.inr l)) : OracleComp _ _)
  | ⟨.inr k, _⟩ => (fun x => (⟨x, fun _ => []⟩ : Message (Fin (k + 1)) (fun _ : Unit => G)))
      <$> (liftM ((unifSpec + (Label →ₒ G)).query (.inl k)) : OracleComp _ _)

/-- Lower an explained interaction to the ordinary hash/coin oracle interface. -/
@[expose] def rawProgram
    (p : OracleComp (explainedSpec F (fun _ : Unit => G) (CoinQuery Label)
      (CoinReply (fun _ => Unit))) α) : OracleComp (unifSpec + (Label →ₒ G)) α :=
  simulateQ rawGame (interactionProgram p)

/-- Any handler that records exactly the reply groups preserves certified explanations. -/
theorem run_receipts_valid [CommSemiring F] [AddCommMonoid G] [Module F G]
    (impl : QueryImpl (plainSpec (fun _ : Unit => G) (CoinQuery Label)
      (CoinReply (fun _ => Unit))) (StateT σ ProbComp))
    (received : σ → List G)
    (hstep : ∀ query st z, z ∈ support ((impl query).run st) →
      received z.2 = received st ++ z.1.groups ())
    (p : OracleComp (explainedSpec F (fun _ : Unit => G) (CoinQuery Label)
      (CoinReply (fun _ => Unit))) (Explained F Unit (fun _ : Unit => G)))
    (st : σ) (hp : IsAlgebraic (fun _ => received st) p) (z)
    (hz : z ∈ support ((simulateQ impl (interactionProgram p)).run st)) :
    z.1.Valid (fun _ => received z.2) := by
  induction p using OracleComp.inductionOn generalizing st z with
  | pure out =>
    simp only [interactionProgram, simulateQ_pure, StateT.run_pure,
      support_pure, Set.mem_singleton_iff] at hz
    subst z
    exact hp
  | query_bind query next ih =>
    simp only [interactionProgram, simulateQ_bind, simulateQ_spec_query,
      StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨w, hw, hz⟩ := hz
    apply ih w.1 w.2 _ z hz
    have hn := ((isAlgebraic_query (Reply := CoinReply (fun _ => Unit))
      (fun _ => received st) query next).mp hp).2 w.1
    change IsAlgebraic (fun _ => received st ++ w.1.groups ()) (next w.1) at hn
    rwa [hstep query.value st w hw]

private theorem table_log [DecidableEq Label] [SampleableType G]
    (g : Fin q → G) (t : (unifSpec + (Label →ₒ G)).Domain)
    (s : SlotRenaming.State Label G q) (z)
    (hz : z ∈ support ((((unifFwdAnswerImpl g).mapStateTBase SlotRenaming.route) t).run s)) :
    z.2.log.map Prod.snd = s.log.map Prod.snd ++
      (match t, z.1 with | .inl _, _ => [] | .inr _, r => [r]) := by
  rw [SlotRenaming.tableHandler_apply] at hz
  cases t with
  | inl k =>
    rw [support_map] at hz
    obtain ⟨r, _, rfl⟩ := hz
    simp
  | inr l =>
    cases hs : s.slotOf l with
    | some i =>
      simp only [hs, support_pure, Set.mem_singleton_iff] at hz
      subst z
      simp [SlotRenaming.record]
    | none =>
      cases hc : s.overflow l with
      | some r =>
        simp only [hs, hc, support_pure, Set.mem_singleton_iff] at hz
        subst z
        simp [SlotRenaming.record]
      | none =>
        by_cases hn : s.next < q
        · simp only [hs, hc, dite_eq_left hn, support_pure, Set.mem_singleton_iff] at hz
          subst z
          simp [SlotRenaming.assign]
        · simp only [hs, hc, dite_eq_right hn, support_map] at hz
          obtain ⟨r, _, rfl⟩ := hz
          simp [SlotRenaming.spill]

/-- A fixed slot table validates the output of a certified interaction over its actual fixed
inputs and chronological hash receipts, including repeated labels and private coins. -/
theorem tableRun_rawProgram_valid [DecidableEq Label] [SampleableType G]
    [CommSemiring F] [AddCommMonoid G] [Module F G]
    (fixed : List G) (g : Fin q → G)
    (p : OracleComp (explainedSpec F (fun _ : Unit => G) (CoinQuery Label)
      (CoinReply (fun _ => Unit))) (Explained F Unit (fun _ : Unit => G)))
    (hp : IsAlgebraic (fun _ => fixed) p) (z)
    (hz : z ∈ support (SlotRenaming.tableRun (rawProgram p) g)) :
    z.1.Valid (fun _ => fixed ++ z.2.log.map Prod.snd) := by
  let impl := (unifFwdAnswerImpl g).mapStateTBase (SlotRenaming.route (D := Label))
  have he : SlotRenaming.tableRun (rawProgram p) g =
      (simulateQ (fun query => simulateQ impl (rawGame query)) (interactionProgram p)).run
        SlotRenaming.initial := by
    rw [SlotRenaming.tableRun, QueryImpl.simulateQ_mapStateTBase_run]
    unfold rawProgram
    rw [← QueryImpl.simulateQ_compose]
    rfl
  rw [he] at hz
  apply run_receipts_valid _ (fun s => fixed ++ s.log.map Prod.snd) ?_ p
    SlotRenaming.initial (by simpa [SlotRenaming.initial] using hp) z hz
  intro query s w hw
  rcases query with ⟨l | k, groups⟩
  · change w ∈ support ((simulateQ impl
      (reply <$> (liftM ((unifSpec + (Label →ₒ G)).query (.inr l)) : OracleComp _ _))).run s) at hw
    simp only [simulateQ_map, simulateQ_spec_query, StateT.run_map, support_map] at hw
    obtain ⟨v, hv, rfl⟩ := hw
    have h := table_log g (.inr l) s v hv
    simpa only [reply, List.append_assoc] using congrArg (fixed ++ ·) h
  · change w ∈ support ((simulateQ impl
      ((fun x => (⟨x, fun _ => []⟩ : Message (Fin (k + 1)) (fun _ : Unit => G))) <$>
        (liftM ((unifSpec + (Label →ₒ G)).query (.inl k)) : OracleComp _ _))).run s) at hw
    simp only [simulateQ_map, simulateQ_spec_query, StateT.run_map, support_map] at hw
    obtain ⟨v, hv, rfl⟩ := hw
    have h := table_log g (.inl k) s v hv
    simpa only [List.append_assoc] using congrArg (fixed ++ ·) h

end GroupModel.HashToGroup
