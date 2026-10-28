/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.GroupModel.HashToGroup.Programmed

/-! # Private coins and coefficient logs

Private uniform samples leave the coefficient cache and chronological receipts unchanged.
The log invariant therefore applies to randomized explained interactions.
-/

public section

namespace GroupModel.HashToGroup

open OracleComp OracleSpec Interaction

variable {Label C D F G κ Data α Query σ : Type} {Reply : Query → Type}

/-- Uniform private coins lifted through a state without changing it. -/
@[expose] def coins : QueryImpl unifSpec (StateT σ ProbComp) :=
  fun n st => (fun x => (x, st)) <$> (liftM (unifSpec.query n) : ProbComp _)

/-- Hash queries and private coins sharing the programmed coefficient state. -/
@[expose] def gameWithCoins [DecidableEq Label] (decode : C → G)
    (sample : Label → ProbComp C) :
    QueryImpl (plainSpec (fun _ : Unit => G) (CoinQuery Label) (CoinReply (fun _ => Unit)))
      (StateT (State Label C) ProbComp) :=
  withCoins coins (game decode sample)

/-- A coin step returns no group inputs and preserves both cache and receipts. -/
@[simp] theorem gameWithCoins_coin [DecidableEq Label] (decode : C → G)
    (sample : Label → ProbComp C) (n : ℕ) (groups : Groups (fun _ : Unit => G))
    (st : State Label C) :
    (gameWithCoins decode sample ⟨.inr n, groups⟩).run st =
      (fun x => (⟨x, fun _ => []⟩, st)) <$> (liftM (unifSpec.query n) : ProbComp _) := by
  change ((fun x : Fin (n + 1) => (⟨x, fun _ => []⟩ : Message (Fin (n + 1))
    (fun _ : Unit => G))) <$> (coins (σ := State Label C) n)).run st = _
  rw [StateT.run_map]
  change (fun z => ((⟨z.1, fun _ => []⟩ : Message (Fin (n + 1))
    (fun _ : Unit => G)), z.2)) <$> ((fun x => (x, st)) <$>
      (liftM (unifSpec.query n) : ProbComp _)) = _
  simp only [Functor.map_map]
  rfl


/-- A hash step uses the cached handler, which appends exactly one receipt. -/
@[simp] theorem gameWithCoins_hash [DecidableEq Label] (decode : C → G)
    (sample : Label → ProbComp C) (l : Label) (groups : Groups (fun _ : Unit => G))
    (st : State Label C) :
    (gameWithCoins decode sample ⟨.inl l, groups⟩).run st =
      (fun z => (reply z.1, z.2)) <$> (oracle decode sample l).run st := by
  change (reply <$> oracle decode sample l).run st = _
  exact StateT.run_map _ _ _

/-- Each step extends the decoded receipts by exactly the groups in its reply. -/
theorem gameWithCoins_receipts [DecidableEq Label] (decode : C → G)
    (sample : Label → ProbComp C)
    (q : Message (CoinQuery Label) (fun _ : Unit => G)) (st : State Label C)
    (z : Message (CoinReply (fun _ : Label => Unit) q.data) (fun _ : Unit => G) ×
      State Label C) (hz : z ∈ support ((gameWithCoins decode sample q).run st)) :
    z.2.2.map decode = st.2.map decode ++ z.1.groups () := by
  rcases q with ⟨l | n, groups⟩
  · change (Message Unit (fun _ : Unit => G) × State Label C) at z
    change z ∈ support ((gameWithCoins decode sample ⟨.inl l, groups⟩).run st) at hz
    rw [gameWithCoins_hash] at hz
    change z ∈ support ((fun w : G × State Label C => (reply w.1, w.2)) <$>
      (oracle decode sample l).run st) at hz
    simp only [support_map, Set.mem_image] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    rw [oracle_apply] at hw
    cases hc : st.1 l with
    | some c => simp only [hc, support_pure, Set.mem_singleton_iff] at hw; subst w; simp [reply]
    | none =>
      simp only [hc, support_map, Set.mem_image] at hw
      obtain ⟨c, _, rfl⟩ := hw
      simp [reply]
  · simp only [gameWithCoins_coin, support_map, Set.mem_image] at hz
    obtain ⟨x, _, rfl⟩ := hz
    simp

/-- Fresh-sample simulation extends to arbitrary interleavings of private coins and hashes. -/
theorem simulateQ_gameWithCoins_mapState [DecidableEq Label] (f : C → D) (decode : D → G)
    (sample : Label → ProbComp C) (target : Label → ProbComp D)
    (h : ∀ l, f <$> sample l =ᵈ target l)
    (p : OracleComp (plainSpec (fun _ : Unit => G) (CoinQuery Label)
      (CoinReply (fun _ => Unit))) α) (st : State Label C) :
    Prod.map id (mapState f) <$> (simulateQ (gameWithCoins (decode ∘ f) sample) p).run st =ᵈ
      (simulateQ (gameWithCoins decode target) p).run (mapState f st) := by
  induction p using OracleComp.inductionOn generalizing st with
  | pure a => simp
  | query_bind q next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
    refine (EvalDistEq.bind_right _ fun (z : Message (CoinReply (fun _ : Label => Unit) q.data)
        (fun _ : Unit => G) × State Label C) => ih z.1 z.2).trans ?_
    have hs : Prod.map id (mapState f) <$>
        (gameWithCoins (decode ∘ f) sample q).run st =ᵈ
        (gameWithCoins decode target q).run (mapState f st) := by
      rcases q with ⟨l | n, groups⟩
      · change Prod.map id (mapState f) <$> (game (decode ∘ f) sample ⟨l, groups⟩).run st =ᵈ
          (game decode target ⟨l, groups⟩).run (mapState f st)
        simpa only [game, StateT.run_map, Functor.map_map, Prod.map, id_eq, Function.comp_def] using
          (oracle_mapState f decode sample target h l st).map (fun z => (reply z.1, z.2))
      · simp
    simpa only [bind_map_left, Prod.map, id_eq] using hs.bind_left
      (fun z => (simulateQ (gameWithCoins decode target) (next z.1)).run z.2)

/-- Execute an explained program through a coin-bearing hash handler, retaining its private log. -/
@[expose] def runGameWithCoins [DecidableEq Label] (decode : C → G)
    (sample : Label → ProbComp C)
    (p : OracleComp (explainedSpec F (fun _ : Unit => G) (CoinQuery Label)
      (CoinReply (fun _ => Unit))) α) (st : State Label C) : ProbComp (α × State Label C) :=
  (simulateQ (gameWithCoins decode sample) (interactionProgram p)).run st

/-- Returning a value leaves the logged execution state unchanged. -/
@[simp] theorem runGameWithCoins_pure [DecidableEq Label] (decode : C → G)
    (sample : Label → ProbComp C) (a : α) (st : State Label C) :
    runGameWithCoins (F := F) decode sample (pure a) st = pure (a, st) := by
  simp [runGameWithCoins, interactionProgram]

private theorem runGameWithCoins_query [DecidableEq Label] (decode : C → G)
    (sample : Label → ProbComp C)
    (q : Explained F (CoinQuery Label) (fun _ : Unit => G))
    (next : Message (CoinReply (fun _ : Label => Unit) q.value.data) (fun _ : Unit => G) →
      OracleComp (explainedSpec F (fun _ : Unit => G) (CoinQuery Label)
        (CoinReply (fun _ => Unit))) α) (st : State Label C) :
    runGameWithCoins decode sample
      (liftM ((explainedSpec F (fun _ : Unit => G) (CoinQuery Label)
        (CoinReply (fun _ => Unit))).query q) >>= next) st =
      (gameWithCoins decode sample q.value).run st >>= fun z =>
        runGameWithCoins decode sample (next z.1) z.2 := by
  simp [runGameWithCoins, interactionProgram]

/-- An explained hash request appends one receipt and continues with its single group reply. -/
theorem runGameWithCoins_hash [DecidableEq Label] (decode : C → G)
    (sample : Label → ProbComp C) (l : Label) (groups : Groups (fun _ : Unit => G))
    (coefficients : Unit → List (List F))
    (next : Message Unit (fun _ : Unit => G) →
      OracleComp (explainedSpec F (fun _ : Unit => G) (CoinQuery Label)
        (CoinReply (fun _ => Unit))) α) (st : State Label C) :
    runGameWithCoins decode sample
      (liftM ((explainedSpec F (fun _ : Unit => G) (CoinQuery Label)
        (CoinReply (fun _ => Unit))).query ⟨⟨.inl l, groups⟩, coefficients⟩) >>= next) st =
      (oracle decode sample l).run st >>= fun z =>
        runGameWithCoins decode sample (next (reply z.1)) z.2 := by
  erw [runGameWithCoins_query]
  rw [gameWithCoins_hash]
  erw [bind_map_left]


/-- An explained private-coin request continues without changing the receipt state. -/
theorem runGameWithCoins_coin [DecidableEq Label] (decode : C → G)
    (sample : Label → ProbComp C) (n : ℕ) (groups : Groups (fun _ : Unit => G))
    (coefficients : Unit → List (List F))
    (next : Message (Fin (n + 1)) (fun _ : Unit => G) →
      OracleComp (explainedSpec F (fun _ : Unit => G) (CoinQuery Label)
        (CoinReply (fun _ => Unit))) α) (st : State Label C) :
    runGameWithCoins decode sample
      (liftM ((explainedSpec F (fun _ : Unit => G) (CoinQuery Label)
        (CoinReply (fun _ => Unit))).query ⟨⟨.inr n, groups⟩, coefficients⟩) >>= next) st =
      (liftM (unifSpec.query n) : ProbComp _) >>= fun x =>
        runGameWithCoins decode sample (next ⟨x, fun _ => []⟩) st := by
  erw [runGameWithCoins_query]
  rw [gameWithCoins_coin]
  erw [bind_map_left]


/-- Run a randomized explained computation and retain the coefficient cache and receipts. -/
@[expose] def runProgramWithCoins [DecidableEq Label] [CommSemiring F] [AddCommMonoid G]
    [Module F G] [Fintype κ] (B : κ → G) (sample : Label → ProbComp (κ → F))
    (p : OracleComp (explainedSpec F (fun _ : Unit => G) (CoinQuery Label)
      (CoinReply (fun _ => Unit))) α) (st : State Label (κ → F)) :
    ProbComp (α × State Label (κ → F)) :=
  runGameWithCoins (basisMap B) sample p st

/-- The coefficient log validates every output of a certified randomized computation. -/
theorem runGameWithCoins_valid [DecidableEq Label] [CommSemiring F] [AddCommMonoid G]
    [Module F G] (decode : C → G) (sample : Label → ProbComp C)
    (p : OracleComp (explainedSpec F (fun _ : Unit => G) (CoinQuery Label)
      (CoinReply (fun _ => Unit))) (Explained F Data (fun _ : Unit => G)))
    (st : State Label C) (hp : IsAlgebraic (fun _ => st.2.map decode) p)
    (z) (hz : z ∈ support (runGameWithCoins decode sample p st)) :
    z.1.Valid (fun _ => z.2.2.map decode) := by
  induction p using OracleComp.inductionOn generalizing st z with
  | pure out =>
    simp only [runGameWithCoins, interactionProgram, simulateQ_pure, StateT.run_pure,
      support_pure, Set.mem_singleton_iff] at hz
    subst z
    exact hp
  | query_bind q next ih =>
    simp only [runGameWithCoins, interactionProgram, simulateQ_bind, simulateQ_spec_query,
      StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨w, hw, hz⟩ := hz
    apply ih w.1 w.2 _ z hz
    have hn := ((isAlgebraic_query (Reply := CoinReply (fun _ => Unit))
      (fun _ => st.2.map decode) q next).mp hp).2 w.1
    change IsAlgebraic (fun _ => st.2.map decode ++ w.1.groups ()) (next w.1) at hn
    rwa [gameWithCoins_receipts decode sample q.value st w hw]

/-- Certified programmed runs with private coins produce valid logged representations. -/
theorem runProgramWithCoins_valid [DecidableEq Label] [CommSemiring F] [AddCommMonoid G]
    [Module F G] [Fintype κ] (B : κ → G) (sample : Label → ProbComp (κ → F))
    (p : OracleComp (explainedSpec F (fun _ : Unit => G) (CoinQuery Label)
      (CoinReply (fun _ => Unit))) (Explained F Data (fun _ : Unit => G)))
    (st : State Label (κ → F)) (hp : IsAlgebraic (fun _ => st.2.map (basisMap B)) p)
    (z) (hz : z ∈ support (runProgramWithCoins B sample p st)) :
    z.1.Valid (fun _ => z.2.2.map (basisMap B)) :=
  runGameWithCoins_valid (basisMap B) sample p st hp z hz

/-- Transport all outputs of a randomized certified computation to the reduction basis. -/
theorem runProgramWithCoins_transport [DecidableEq Label] [CommSemiring F] [AddCommMonoid G]
    [Module F G] [Fintype κ] (B : κ → G) (sample : Label → ProbComp (κ → F))
    (p : OracleComp (explainedSpec F (fun _ : Unit => G) (CoinQuery Label)
      (CoinReply (fun _ => Unit))) (Explained F Data (fun _ : Unit => G)))
    (st : State Label (κ → F)) (hp : IsAlgebraic (fun _ => st.2.map (basisMap B)) p)
    (z) (hz : z ∈ support (runProgramWithCoins B sample p st)) :
    (transportExplained (fun _ => z.2.2) z.1 ()).map (basisMap B) = z.1.value.groups () :=
  transportExplained_evaluate (fun _ => B) (fun _ => z.2.2) z.1
    (runProgramWithCoins_valid B sample p st hp z hz) ()

private theorem run_project [DecidableEq Label] (decode : C → G) (sample : Label → ProbComp C)
    (p : OracleComp (explainedSpec F (fun _ : Unit => G) (CoinQuery Label)
      (CoinReply (fun _ => Unit))) α) (st : State Label C)
    (basis : Groups (fun _ : Unit => G)) :
    Prod.map Prod.fst id <$> ((simulateQ
      (fun (q : Explained F (CoinQuery Label) (fun _ : Unit => G)) =>
        StateT.mk fun received => do
      let r ← gameWithCoins decode sample q.value
      pure (r, extend received r.groups)) p).run basis).run st =
      runGameWithCoins decode sample p st := by
  induction p using OracleComp.inductionOn generalizing st basis with
  | pure a => simp [runGameWithCoins, interactionProgram]
  | query_bind q next ih =>
    simp only [runGameWithCoins, interactionProgram, simulateQ_bind, simulateQ_spec_query,
      StateT.run_bind, StateT.run_mk, map_bind, bind_assoc, pure_bind]
    apply bind_congr
    intro z
    exact ih z.1 z.2 (extend basis z.1.groups)

/-- Forgetting Interaction's duplicate receipt counter leaves exactly the logged execution. -/
theorem runGameWithCoins_run [DecidableEq Label] [CommSemiring F] [AddCommMonoid G]
    [Module F G] (decode : C → G) (sample : Label → ProbComp C)
    (A : Adversary F (fun _ : Unit => G) Unit (CoinQuery Label)
      (CoinReply (fun _ => Unit)) Data)
    (input : Message Unit (fun _ : Unit => G)) (st : State Label C) :
    Prod.map Prod.fst id <$> (A.run (gameWithCoins decode sample) input).run st =
      runGameWithCoins decode sample (A.main input) st :=
  run_project decode sample (A.main input) st input.groups

end GroupModel.HashToGroup
