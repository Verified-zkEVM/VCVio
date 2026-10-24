/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.ShareBound
public import HashSig.SLHDSA.SHAKE128s.Proof.VerificationBudget

/-!
# The blind verifier's probes are filed

`visible` reads the open table first and the oracle's cache after it, in the order the blind
router (`route false`) answers. Along a run of world queries the served digests do not move, so
the open table does not either; the cache only grows, and an input the open table lacks stays
lacked. So every answer a blind world step takes is the one `visible` gives at the end of the run,
and replaying a hash computation at the final visible cache consults only inputs the run filed,
each at the digests served when the run began. This holds at any step that routes a hash input
blindly and files it (`RoutesBlind`), whatever else the state carries:

* at the flag-free blind step `ShareBlindFacts.blindStep` (`blind_probes_filed`, and at the
  verifier `blind_verify_probes_filed`);
* at the flagged blind handler, from any flag (`probes_filed`, `verify_probes_filed_any`) — world
  steps never read the flag.

No cold cache is needed for this. The cold cache (`ColdCache`) is the separate fact that a blind
run that ends with the flag down never cached an input of the walk's warm cache.
-/

public section

open OracleComp OracleSpec

namespace SlhDsaSecurity.ShareFiled

variable {α : Type}

open Security CanonicalGraph ShareGame

/-! ## The cold cache -/

/-- What a blind routed query does to the cache: nothing, or it caches an input the open table
lacks and the cache did not hold. -/
theorem route_false_cases (setup : Setup) (state : St) (input : Bytes) (z : HashOutput × St)
    (hz : z ∈ support (route false setup state input)) :
    (openAt setup state.served input = some z.1 ∧ z.2 = state) ∨
      (openAt setup state.served input = none ∧ state.cache input = some z.1 ∧ z.2 = state) ∨
        (openAt setup state.served input = none ∧ state.cache input = none ∧
          z.2 = { state with cache := state.cache.cacheQuery input z.1 }) := by
  classical
  unfold route at hz
  rw [ite_eq_right Bool.false_ne_true] at hz
  cases hopen : openAt setup state.served input with
  | some answer =>
    simp only [hopen, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact Or.inl ⟨rfl, rfl⟩
  | none =>
    simp only [hopen, Bool.false_eq_true, false_and, ite_false] at hz
    unfold plain at hz
    cases hcached : state.cache input with
    | some answer =>
      simp only [hcached, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)
    | none =>
      simp only [hcached, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
      obtain ⟨value, -, rfl⟩ := hz
      exact Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)

/-! ## A step that routes blindly and files -/

/-- **The visible cache grows** from one state to the next: every visible entry stays. -/
@[expose] def Grows (setup : Setup) (old new : St) : Prop :=
  ∀ input value, visible setup old input = some value → visible setup new input = some value

theorem Grows.refl (setup : Setup) (state : St) : Grows setup state state := fun _ _ h => h

theorem Grows.trans {setup : Setup} {first second third : St} (h1 : Grows setup first second)
    (h2 : Grows setup second third) : Grows setup first third :=
  fun x v h => h2 x v (h1 x v h)

/-- **A hash handler that routes blindly and files**, read through a projection to the game's
state: each step answers as the blind router does and files the input at the served digests. -/
@[expose] def RoutesBlind (setup : Setup) {σ : Type} (π : σ → St)
    (impl : QueryImpl HashSpec (StateT σ ProbComp)) : Prop :=
  ∀ input state z, z ∈ support ((impl input).run state) →
    ∃ routed ∈ support (route false setup (π state) input), z.1 = routed.1 ∧
      π z.2 = { routed.2 with record := (π state).record ++ [(input, (π state).served)] }

/-- **One blind routed step, filed**: the digests stay, the input is filed at them, the visible
cache grows, and it answers the input as the step did. -/
theorem routed_step (setup : Setup) (state : St) (input : Bytes) (routed : HashOutput × St)
    (hrouted : routed ∈ support (route false setup state input)) :
    let next : St := { routed.2 with record := state.record ++ [(input, state.served)] }
    next.served = state.served ∧ next.record = state.record ++ [(input, state.served)] ∧
      Grows setup state next ∧ visible setup next input = some routed.1 := by
  intro next
  obtain ⟨hserved, -, -⟩ := ShareFlag.route_mem_support false setup state input routed hrouted
  have hserved' : next.served = state.served := hserved
  refine ⟨hserved', rfl, ?_, ?_⟩
  · intro x v hx
    unfold visible at hx ⊢
    rw [QueryCache.ofFn_apply] at hx ⊢
    rw [hserved']
    cases hopen : openAt setup state.served x with
    | some answer =>
      rw [hopen] at hx
      exact hx
    | none =>
      rw [hopen] at hx
      simp only at hx ⊢
      change routed.2.cache x = some v
      rcases route_false_cases setup state input routed hrouted with
        ⟨-, h⟩ | ⟨-, -, h⟩ | ⟨-, hcached, h⟩
      · rw [h]; exact hx
      · rw [h]; exact hx
      · rw [h]
        by_cases hxi : x = input
        · subst hxi
          rw [hcached] at hx
          cases hx
        · simpa [QueryCache.cacheQuery_of_ne _ _ hxi] using hx
  · unfold visible
    rw [QueryCache.ofFn_apply]
    rw [hserved']
    rcases route_false_cases setup state input routed hrouted with
      ⟨hopen, -⟩ | ⟨hopen, hcached, h⟩ | ⟨hopen, -, h⟩
    · rw [hopen]
    · rw [hopen]
      change routed.2.cache input = some routed.1
      rw [h]; exact hcached
    · rw [hopen]
      change routed.2.cache input = some routed.1
      rw [h]; exact QueryCache.cacheQuery_self _ _ _

/-- **One step of a handler that routes blindly and files.** -/
theorem hash_step (setup : Setup) {σ : Type} (π : σ → St)
    (impl : QueryImpl HashSpec (StateT σ ProbComp)) (himpl : RoutesBlind setup π impl)
    (input : Bytes) (state : σ) (step : HashOutput × σ)
    (hstep : step ∈ support ((impl input).run state)) :
    (π step.2).served = (π state).served ∧
      (π step.2).record = (π state).record ++ [(input, (π state).served)] ∧
        Grows setup (π state) (π step.2) ∧ visible setup (π step.2) input = some step.1 := by
  obtain ⟨routed, hrouted, hanswer, hnext⟩ := himpl input state step hstep
  rw [hnext, hanswer]
  exact routed_step setup (π state) input routed hrouted

/-- **Along a run of a handler that routes blindly and files**: the digests stay, the record only
grows, and the visible cache grows. -/
theorem hash_run (setup : Setup) {σ : Type} (π : σ → St)
    (impl : QueryImpl HashSpec (StateT σ ProbComp)) (himpl : RoutesBlind setup π impl)
    {α : Type} (computation : OracleComp HashSpec α) :
    ∀ (state : σ), ∀ z ∈ support ((simulateQ impl computation).run state),
      (π z.2).served = (π state).served ∧ (π state).record <+: (π z.2).record ∧
        Grows setup (π state) (π z.2) := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
    intro state z hz
    rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨rfl, List.prefix_refl _, Grows.refl _ _⟩
  | query_bind input next ih =>
    intro state z hz
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨step, hstep, hrest⟩ := hz
    obtain ⟨hserved, hrecord, hgrows, -⟩ := hash_step setup π impl himpl input state step hstep
    obtain ⟨hserved', hprefix', hgrows'⟩ := ih step.1 step.2 z hrest
    refine ⟨hserved'.trans hserved, ?_, hgrows.trans hgrows'⟩
    exact (List.prefix_append _ _).trans (hrecord ▸ hprefix')

/-- **Every probe a replay at the final visible cache consults was filed at the starting
digests**, along a run of a handler that routes blindly and files. -/
theorem probe_filed (setup : Setup) {σ : Type} (π : σ → St)
    (impl : QueryImpl HashSpec (StateT σ ProbComp)) (himpl : RoutesBlind setup π impl)
    {α : Type} (computation : OracleComp HashSpec α) (probe : Bytes) (final : St)
    (hquery : CacheReplay.QueriesUnder (visible setup final) computation probe) :
    ∀ (state : σ), ∀ z ∈ support ((simulateQ impl computation).run state), π z.2 = final →
      (probe, (π state).served) ∈ final.record := by
  induction hquery with
  | head input next =>
    intro state z hmem hfinal
    rw [simulateQ_bind, show simulateQ impl (query (spec := HashSpec) input) =
        impl input from by simp, StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨step, hstep, hrest⟩ := hmem
    obtain ⟨-, hrecord, -, -⟩ := hash_step setup π impl himpl input state step hstep
    obtain ⟨-, hprefix, -⟩ := hash_run setup π impl himpl (next step.1) step.2 z hrest
    rw [← hfinal]
    refine hprefix.subset ?_
    rw [hrecord]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  | tail input probe next _ ih =>
    intro state z hmem hfinal
    rw [simulateQ_bind, show simulateQ impl (query (spec := HashSpec) input) =
        impl input from by simp, StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨step, hstep, hrest⟩ := hmem
    obtain ⟨hserved, -, -, hvisible⟩ := hash_step setup π impl himpl input state step hstep
    obtain ⟨-, -, hgrows⟩ := hash_run setup π impl himpl (next step.1) step.2 z hrest
    have hreplay : CacheReplay.replay (visible setup final) input = step.1 := by
      rw [← hfinal]
      simp [CacheReplay.replay, hgrows input step.1 hvisible]
    rw [← hserved]
    exact ih step.2 z (by rw [hreplay]; exact hrest) hfinal

/-- **A world run of a lifted hash computation** at a handler whose hash steps route blindly and
file keeps the digests, and every probe a replay of the computation at the final visible cache
consults is filed in the record at the starting digests. -/
theorem probes_filed_of (setup : Setup) {σ : Type} (π : σ → St)
    (coin : QueryImpl unifSpec (StateT σ ProbComp))
    (impl : QueryImpl HashSpec (StateT σ ProbComp)) (himpl : RoutesBlind setup π impl)
    {α : Type} (computation : OracleComp HashSpec α) (state : σ) (z : α × σ)
    (hz : z ∈ support ((simulateQ (coin + impl)
      (OracleComp.liftComp computation OracleWorld)).run state)) :
    (π z.2).served = (π state).served ∧
      ∀ probe, CacheReplay.QueriesUnder (visible setup (π z.2)) computation probe →
        (probe, (π state).served) ∈ (π z.2).record := by
  rw [QueryImpl.simulateQ_add_liftComp_right] at hz
  exact ⟨(hash_run setup π impl himpl computation state z hz).1, fun probe hprobe =>
    probe_filed setup π impl himpl computation probe _ hprobe state z hz rfl⟩

/-! ## At the flag-free blind step -/

/-! ## At the flagged blind handler, from any flag -/

theorem worldImpl_run (lenient : Bool) (setup : Setup) (world : OracleWorld.Domain)
    (p : St × Bool) :
    ((ShareBound.worldImpl lenient setup) world).run p =
      ((handler lenient setup) (worldQuery world)).run p := by
  change (simulateQ (handler lenient setup) (query (spec := ShareSpec) (worldQuery world) :
    OracleComp ShareSpec (OracleWorld.Range world))).run p = _
  erw [simulateQ_spec_query]

/-- The blind world handler at a hash input. -/
@[expose]
noncomputable def hashImpl (setup : Setup) : QueryImpl HashSpec (StateT (St × Bool) ProbComp) :=
  fun input => ShareBound.worldImpl false setup (Sum.inr input)

/-- The blind world handler at a coin. -/
@[expose]
noncomputable def coinImpl (setup : Setup) : QueryImpl unifSpec (StateT (St × Bool) ProbComp) :=
  fun coin => ShareBound.worldImpl false setup (Sum.inl coin)

theorem worldImpl_eq_add (setup : Setup) :
    ShareBound.worldImpl false setup = coinImpl setup + hashImpl setup := by
  funext queried
  rcases queried with coin | input <;> rfl

open scoped Classical in
theorem hashImpl_run (setup : Setup) (input : Bytes) (p : St × Bool) :
    (hashImpl setup input).run p = (do
      let step ← route false setup p.1 input
      pure (step.1, ({ step.2 with record := p.1.record ++ [(input, p.1.served)] },
        p.2 || decide (¬ setup.Good ∨ Guess setup p.1.served input)))) := by
  change ((ShareBound.worldImpl false setup) (Sum.inr input)).run p = _
  rw [worldImpl_run]
  rfl

theorem routesBlind_hashImpl (setup : Setup) :
    RoutesBlind setup Prod.fst (hashImpl setup) := by
  classical
  intro input state z hz
  rw [hashImpl_run, mem_support_bind_iff] at hz
  obtain ⟨routed, hrouted, hz⟩ := hz
  rw [support_pure, Set.mem_singleton_iff] at hz
  subst hz
  exact ⟨routed, hrouted, rfl, rfl⟩

/-- **A blind world run of a lifted hash computation**, from any flag, keeps the digests, and
every probe a replay of the computation at the final visible cache consults is filed in the
record at the starting digests. -/
theorem probes_filed {α : Type} (setup : Setup) (computation : OracleComp HashSpec α)
    (p : St × Bool) (z : α × (St × Bool))
    (hz : z ∈ support ((simulateQ (ShareBound.worldImpl false setup)
      (OracleComp.liftComp computation OracleWorld)).run p)) :
    z.2.1.served = p.1.served ∧
      ∀ probe, CacheReplay.QueriesUnder (visible setup z.2.1) computation probe →
        (probe, p.1.served) ∈ z.2.1.record := by
  rw [worldImpl_eq_add] at hz
  exact probes_filed_of setup Prod.fst (coinImpl setup) (hashImpl setup)
    (routesBlind_hashImpl setup) computation p z hz

/-- **At the verifier, run on the world** as the share game runs it, from any flag. -/
theorem verify_probes_filed_any (setup : Setup) (pk : PublicKey) (request : Message)
    (wire : Bytes) (p : St × Bool) (w : Bool × (St × Bool))
    (hw : w ∈ support ((simulateQ (ShareBound.worldImpl false setup)
      (Scheme.verify (m := OracleComp OracleWorld) pk request wire)).run p)) :
    w.2.1.served = p.1.served ∧
      ∀ probe, CacheReplay.QueriesUnder (visible setup w.2.1)
          (Scheme.verify (m := OracleComp HashSpec) pk request wire) probe →
        (probe, p.1.served) ∈ w.2.1.record := by
  rw [VerificationBudget.verify_lift] at hw
  exact probes_filed setup _ p w hw

end SlhDsaSecurity.ShareFiled
