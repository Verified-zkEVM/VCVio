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
@[expose, simps -isSimp] def rawGame :
    QueryImpl (plainSpec (fun _ : Unit => G) (CoinQuery Label) (CoinReply (fun _ => Unit)))
      (OracleComp (unifSpec + (Label →ₒ G))) where
  toFun
  | ⟨.inl l, _⟩ => reply <$> (liftM ((unifSpec + (Label →ₒ G)).query (.inr l)) : OracleComp _ _)
  | ⟨.inr k, _⟩ => (fun x => (⟨x, fun _ => []⟩ : Message (Fin (k + 1)) (fun _ : Unit => G)))
      <$> (liftM ((unifSpec + (Label →ₒ G)).query (.inl k)) : OracleComp _ _)

/-- Lower an explained interaction to the ordinary hash/coin oracle interface. -/
@[expose] def rawProgram
    (p : OracleComp (explainedSpec F (fun _ : Unit => G) (CoinQuery Label)
      (CoinReply (fun _ => Unit))) α) : OracleComp (unifSpec + (Label →ₒ G)) α :=
  simulateQ rawGame (interactionProgram p)

/-- A returned value makes no raw queries. -/
@[simp] theorem rawProgram_pure (a : α) :
    rawProgram (pure a : OracleComp (explainedSpec F (fun _ : Unit => G) (CoinQuery Label)
      (CoinReply (fun _ => Unit))) α) = pure a := by
  simp [rawProgram, interactionProgram]

/-- An explained hash request is one raw hash query. -/
theorem rawProgram_hash (l : Label) (groups : Groups (fun _ : Unit => G))
    (coefficients : Unit → List (List F))
    (next : Message Unit (fun _ : Unit => G) →
      OracleComp (explainedSpec F (fun _ : Unit => G) (CoinQuery Label)
        (CoinReply (fun _ => Unit))) α) :
    rawProgram (liftM ((explainedSpec F (fun _ : Unit => G) (CoinQuery Label)
      (CoinReply (fun _ => Unit))).query ⟨⟨.inl l, groups⟩, coefficients⟩) >>= next) =
      liftM ((unifSpec + (Label →ₒ G)).query (.inr l)) >>= fun g =>
        rawProgram (next (reply g)) :=
  rfl

/-- An explained private-coin request is one raw uniform query. -/
theorem rawProgram_coin (k : ℕ) (groups : Groups (fun _ : Unit => G))
    (coefficients : Unit → List (List F))
    (next : Message (Fin (k + 1)) (fun _ : Unit => G) →
      OracleComp (explainedSpec F (fun _ : Unit => G) (CoinQuery Label)
        (CoinReply (fun _ => Unit))) α) :
    rawProgram (liftM ((explainedSpec F (fun _ : Unit => G) (CoinQuery Label)
      (CoinReply (fun _ => Unit))).query ⟨⟨.inr k, groups⟩, coefficients⟩) >>= next) =
      liftM ((unifSpec + (Label →ₒ G)).query (.inl k)) >>= fun x =>
        rawProgram (next ⟨x, fun _ => []⟩) :=
  rfl

private theorem table_log [DecidableEq Label] [SampleableType G]
    (g : Fin q → G) (t : (unifSpec + (Label →ₒ G)).Domain)
    (s : SlotRenaming.State Label G q) (z)
    (hz : z ∈ support ((((unifFwdAnswerImpl ⟨g⟩).mapStateTBase SlotRenaming.route) t).run s)) :
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
  let impl := (unifFwdAnswerImpl ⟨g⟩).mapStateTBase (SlotRenaming.route (D := Label))
  have he : SlotRenaming.tableRun (rawProgram p) g =
      (simulateQ (⟨fun query => simulateQ impl (rawGame query)⟩ :
        QueryImpl _ (StateT _ ProbComp)) (interactionProgram p)).run
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

/-! ## The recording oracle

The raw execution is a run of the hash-to-group oracle itself, with every receipt tagged by its
origin. -/

/-- The state of the origin-recording oracle read from a label cache and a chronological label
log, with the fixed inputs received first. -/
@[expose] def receiptState (fixed : Fin n → G)
    (s : (Label →ₒ G).QueryCache × List (Label × G)) : State Label (Receipt n Label G) :=
  (QueryCache.ofFn fun l => (s.1 l).map fun g => (Sum.inr l, g),
    List.ofFn (fun i => (Sum.inl i, fixed i)) ++ s.2.map fun r => (Sum.inr r.1, r.2))

private theorem receiptCache_cacheQuery [DecidableEq Label]
    (c : (Label →ₒ G).QueryCache) (l : Label) (g : G) :
    QueryCache.ofFn (spec := Label →ₒ Receipt n Label G)
        (fun k => ((c.cacheQuery l g) k).map fun g => (Sum.inr k, g)) =
      (QueryCache.ofFn (spec := Label →ₒ Receipt n Label G)
        fun k => (c k).map fun g => (Sum.inr k, g)).cacheQuery l (Sum.inr l, g) := by
  ext k
  by_cases h : k = l
  · subst k; simp
  · simp [h]

/-- Running the raw program against the lazy random oracle is running the interaction against the
hash-to-group oracle that records each receipt's origin, exactly: the output, the cache and the
chronological receipts all agree. -/
theorem map_run_simulateQ_honest_rawProgram [DecidableEq Label] [SampleableType G]
    (fixed : Fin n → G)
    (p : OracleComp (explainedSpec F (fun _ : Unit => G) (CoinQuery Label)
      (CoinReply (fun _ => Unit))) α)
    (s : (Label →ₒ G).QueryCache × List (Label × G)) :
    Prod.map id (receiptState fixed) <$>
        (simulateQ SlotRenaming.honest (rawProgram p)).run s =
      runGameWithCoins Prod.snd (provenanceSample n fun _ => $ᵗ G) p (receiptState fixed s) := by
  unfold runGameWithCoins rawProgram
  rw [← QueryImpl.simulateQ_compose]
  apply map_run_simulateQ_eq_of_query_map_eq
  rintro ⟨l | k, groups⟩ ⟨c, log⟩
  · change Prod.map id (receiptState fixed) <$> (simulateQ SlotRenaming.honest
      (reply <$> (liftM ((unifSpec + (Label →ₒ G)).query (.inr l)) : OracleComp _ _))).run
        (c, log) = _
    rw [gameWithCoins_hash, oracle_apply]
    simp only [simulateQ_map, simulateQ_spec_query, StateT.run_map, Functor.map_map]
    change _ <$> ((fun z => (z.1, z.2, log ++ [(l, z.1)])) <$>
      ((Label →ₒ G).randomOracle l).run c) = _
    cases hc : c l with
    | some g =>
      rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_some _ hc]
      simp [receiptState, hc]
    | none =>
      rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_none _ hc]
      simp only [receiptState, Functor.map_map, Prod.map, id_eq, provenanceSample,
        uniformSampleImpl, QueryCache.ofFn_apply, hc, Option.map_none, receiptCache_cacheQuery,
        List.map_append, List.map_cons, List.map_nil, List.append_assoc]
  · rw [gameWithCoins_coin]
    change Prod.map id (receiptState fixed) <$> (simulateQ SlotRenaming.honest
      ((fun x => (⟨x, fun _ => []⟩ : Message (Fin (k + 1)) (fun _ : Unit => G))) <$>
        (liftM ((unifSpec + (Label →ₒ G)).query (.inl k)) : OracleComp _ _))).run (c, log) = _
    simp only [simulateQ_map, simulateQ_spec_query, StateT.run_map, Functor.map_map]
    change _ <$> ((fun x => (x, (c, log))) <$> (liftM (unifSpec.query k) : ProbComp _)) = _
    simp only [Functor.map_map, Prod.map, id_eq]
    rfl

end GroupModel.HashToGroup
