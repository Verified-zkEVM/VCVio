/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Statement.Game

/-!
# Transferring security bits along a relabelling of hash answers

Two pure-mode signature schemes over the same byte-string hash oracle may represent its answers
differently, say as `A` and as `B`, related by a bijection `e : A ≃ B`. This file shows that
security bits transfer from one to the other when the schemes agree up to that bijection.

* `relabel e` runs a program of the `A` world in the `B` world: uniform queries pass through and
  each hash answer is read back with `e.symm`; `unlabel e` is its inverse
  (`simulateQ_relabel_unlabel`, `simulateQ_unlabel_relabel`).
* When `e` carries the uniform sampler of `A` to that of `B`, relabelling does not change the law
  of a run in the random-oracle model (`run_simulateQ_relabel`): the two lazily sampled caches
  stay related by `e` throughout (`run_simulateQ_relabel_from`).
* Relabelling issues one hash query per hash query, so it commutes with hash counting
  (`simulateQ_relabel_countAllHashes`, `simulateQ_relabel_countQueries`).
* A `SchemeBridge` records that signing and verification agree through `relabel e` and that the
  two key generations, followed by any continuation, have the same law; `keygen_of_seeds` derives
  the latter from equal-in-law seed draws followed by equal programs. An adversary against the
  `B` scheme then becomes one against the `A` scheme (`adapt`) whose experiment has the same law
  (`experiment_evalDistEq`), so security bits transfer (`hasSecurityBits_of_bridge`).
-/

public section

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.Bridge

variable {A B : Type}

/-! ## Relabelling the hash oracle -/

/-- Run a query of the `A` world in the `B` world: a uniform query is asked unchanged, and a
hash query is asked of `B`'s oracle with its answer read back through `e.symm`. -/
@[expose] def relabel (e : A ≃ B) : QueryImpl (Game.World A) (OracleComp (Game.World B))
  | .inl n => liftM ((Game.World B).query (.inl n))
  | .inr x => e.symm <$> liftM ((Game.World B).query (.inr x))

/-- Run a query of the `B` world in the `A` world: a uniform query is asked unchanged, and a
hash query is asked of `A`'s oracle with its answer read back through `e`. -/
@[expose] def unlabel (e : A ≃ B) : QueryImpl (Game.World B) (OracleComp (Game.World A))
  | .inl n => liftM ((Game.World A).query (.inl n))
  | .inr x => e <$> liftM ((Game.World A).query (.inr x))

/-- Relabelling a uniform query asks it unchanged. -/
@[simp]
theorem relabel_apply_inl (e : A ≃ B) (n : ℕ) :
    relabel e (.inl n) = liftM ((Game.World B).query (.inl n)) := rfl

/-- Relabelling a hash query reads `B`'s answer back through `e.symm`. -/
@[simp]
theorem relabel_apply_inr (e : A ≃ B) (x : Bytes) :
    relabel e (.inr x) = e.symm <$> liftM ((Game.World B).query (.inr x)) := rfl

/-- Unlabelling a uniform query asks it unchanged. -/
@[simp]
theorem unlabel_apply_inl (e : A ≃ B) (n : ℕ) :
    unlabel e (.inl n) = liftM ((Game.World A).query (.inl n)) := rfl

/-- Unlabelling a hash query reads `A`'s answer back through `e`. -/
@[simp]
theorem unlabel_apply_inr (e : A ≃ B) (x : Bytes) :
    unlabel e (.inr x) = e <$> liftM ((Game.World A).query (.inr x)) := rfl

/-- Unlabelling and then relabelling a program of the `B` world gives the program back. -/
theorem simulateQ_relabel_unlabel (e : A ≃ B) {α : Type} (P : OracleComp (Game.World B) α) :
    simulateQ (relabel e) (simulateQ (unlabel e) P) = P := by
  rw [QueryImpl.simulateQ_simulateQ_eq_of_apply (impl := QueryImpl.id' _), simulateQ_id']
  rintro (n | x) <;> simp

/-- Relabelling and then unlabelling a program of the `A` world gives the program back. -/
theorem simulateQ_unlabel_relabel (e : A ≃ B) {α : Type} (P : OracleComp (Game.World A) α) :
    simulateQ (unlabel e) (simulateQ (relabel e) P) = P := by
  rw [QueryImpl.simulateQ_simulateQ_eq_of_apply (impl := QueryImpl.id' _), simulateQ_id']
  rintro (n | x) <;> simp

/-! ## The random oracle under relabelling -/

/-- The cache of the random oracle with answers in `Output`. -/
abbrev Cache (Output : Type) := (Xmss.RandomOracleModel.HashSpec Bytes Output).QueryCache

/-- The cache whose entries are those of `cache` mapped through `e`. -/
@[expose] def mapCache (e : A ≃ B) (cache : Cache A) : Cache B :=
  QueryCache.ofFn fun x => (cache x).map e

/-- Mapping the empty cache gives the empty cache. -/
theorem mapCache_empty (e : A ≃ B) : mapCache e ∅ = ∅ :=
  QueryCache.ext fun x => by simp [mapCache]

/-- Mapping a cache commutes with recording an answer, mapped through `e`. -/
theorem mapCache_cacheQuery (e : A ≃ B) (cache : Cache A) (x : Bytes) (a : A) :
    mapCache e (cache.cacheQuery x a) = (mapCache e cache).cacheQuery x (e a) := by
  refine QueryCache.ext fun y => ?_
  by_cases h : y = x
  · subst h
    simp [mapCache]
  · simp [mapCache, QueryCache.cacheQuery, h]

/-- State-map transport in distribution: if each step of `left` from the image of a state has the
law of the corresponding step of `right` with its final state mapped by `proj`, then the same
holds for the whole simulated run of any program. -/
theorem simulateQ_run_evalDistEq_map {ι : Type} {spec : OracleSpec ι} {σ τ : Type}
    (left : QueryImpl spec (StateT τ ProbComp)) (right : QueryImpl spec (StateT σ ProbComp))
    (proj : σ → τ)
    (h : ∀ t s, (left t).run (proj s) =ᵈ Prod.map id proj <$> (right t).run s)
    {α : Type} (P : OracleComp spec α) (s : σ) :
    (simulateQ left P).run (proj s) =ᵈ Prod.map id proj <$> (simulateQ right P).run s := by
  induction P using OracleComp.inductionOn generalizing s with
  | pure x =>
    simp only [simulateQ_pure, StateT.run_pure, map_pure]
    exact EvalDistEq.rfl
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, id_map,
      OracleQuery.input_query, StateT.run_bind, map_bind]
    refine ((h t s).bind fun p =>
      EvalDistEq.rfl (mx := (simulateQ left (k p.1)).run p.2)).trans ?_
    rw [bind_map_left]
    exact EvalDistEq.bind_right _ fun p => ih p.1 p.2

section Uniform

variable [SampleableType A] [SampleableType B]

/-- One relabelled query, answered by `B`'s random oracle from the mapped cache, has the law of
the query answered by `A`'s random oracle with its final cache mapped, provided `e` carries the
uniform sampler of `A` to that of `B`. -/
theorem relabel_step (e : A ≃ B) (he : (e <$> ($ᵗ A : ProbComp A)) =ᵈ ($ᵗ B : ProbComp B))
    (t : (Game.World A).Domain) (cache : Cache A) :
    (simulateQ (Xmss.RandomOracleModel.impl Bytes B) (relabel e t)).run (mapCache e cache) =ᵈ
      Prod.map id (mapCache e) <$> (Xmss.RandomOracleModel.impl Bytes A t).run cache := by
  rcases t with n | x
  · simp [Xmss.RandomOracleModel.impl, unifFwdImpl]
  · simp only [relabel, Xmss.RandomOracleModel.impl, simulateQ_map, StateT.run_map,
      QueryImpl.add_apply_inr]
    rw [simulateQ_spec_query, QueryImpl.add_apply_inr, randomOracle.run_eq,
      randomOracle.run_eq]
    cases h : cache x with
    | some a =>
      have hmap : (mapCache e cache) x = some (e a) := by simp [mapCache, h]
      simp [hmap]
    | none =>
      have hmap : (mapCache e cache) x = none := by simp [mapCache, h]
      simp only [hmap, map_bind, map_pure]
      have key := he.symm.map (fun b => (e.symm b, (mapCache e cache).cacheQuery x b))
      rw [Functor.map_map] at key
      simp only [Equiv.symm_apply_apply, ← mapCache_cacheQuery] at key
      rw [map_eq_bind_pure_comp, map_eq_bind_pure_comp] at key
      exact key

/-- A relabelled program run against `B`'s random oracle from a mapped cache has the law of the
program run against `A`'s random oracle, with its final cache mapped. -/
theorem run_simulateQ_relabel_from (e : A ≃ B)
    (he : (e <$> ($ᵗ A : ProbComp A)) =ᵈ ($ᵗ B : ProbComp B))
    {α : Type} (P : OracleComp (Game.World A) α) (cache : Cache A) :
    (simulateQ (Xmss.RandomOracleModel.impl Bytes B) (simulateQ (relabel e) P)).run
        (mapCache e cache) =ᵈ
      Prod.map id (mapCache e) <$>
        (simulateQ (Xmss.RandomOracleModel.impl Bytes A) P).run cache := by
  rw [← QueryImpl.simulateQ_compose]
  exact simulateQ_run_evalDistEq_map _ _ (mapCache e) (fun t s => relabel_step e he t s) P cache

/-- **Relabelling preserves the random-oracle model.** If `e` carries the uniform sampler of `A`
to that of `B`, a relabelled program has the same law in the random-oracle model as the
original. -/
theorem run_simulateQ_relabel (e : A ≃ B)
    (he : (e <$> ($ᵗ A : ProbComp A)) =ᵈ ($ᵗ B : ProbComp B))
    {α : Type} (P : OracleComp (Game.World A) α) :
    Xmss.RandomOracleModel.run (simulateQ (relabel e) P) =ᵈ Xmss.RandomOracleModel.run P := by
  have h := (run_simulateQ_relabel_from e he P ∅).map Prod.fst
  rw [mapCache_empty] at h
  simpa [Xmss.RandomOracleModel.run, StateT.run'_eq, Functor.map_map] using h

end Uniform

/-! ## Relabelling and counting -/

/-- Writer-level simulation collapse: if a writer-instrumented handler `red` followed by `impl`
agrees on every query with `game`, then it agrees on every program. -/
theorem simulateQ_writerT_run_compose {ι₁ ι₂ : Type} {spec₁ : OracleSpec ι₁}
    {spec₂ : OracleSpec ι₂} {ω : Type} [Monoid ω] {n : Type → Type} [Monad n] [LawfulMonad n]
    (red : QueryImpl spec₁ (WriterT ω (OracleComp spec₂))) (impl : QueryImpl spec₂ n)
    (game : QueryImpl spec₁ (WriterT ω n))
    (bridge : ∀ q, simulateQ impl (red q).run = (game q).run) {α : Type}
    (oa : OracleComp spec₁ α) :
    simulateQ impl (simulateQ red oa).run = (simulateQ game oa).run := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t f ih =>
    simp only [simulateQ_bind, WriterT.run_bind, simulateQ_spec_query, bridge t, simulateQ_map]
    exact bind_congr fun p => by rw [ih p.1]

/-- Simulation collapse through a writer over a state: if a handler `red` into
`WriterT ω (StateT σ (OracleComp spec₂))` followed by `impl` agrees on every query and state with
`game`, then it agrees on every program and state. -/
theorem simulateQ_writerT_stateT_run_compose {ι₁ ι₂ : Type} {spec₁ : OracleSpec ι₁}
    {spec₂ : OracleSpec ι₂} {ω σ : Type} [Monoid ω] {n : Type → Type} [Monad n] [LawfulMonad n]
    (red : QueryImpl spec₁ (WriterT ω (StateT σ (OracleComp spec₂)))) (impl : QueryImpl spec₂ n)
    (game : QueryImpl spec₁ (WriterT ω (StateT σ n)))
    (bridge : ∀ q s, simulateQ impl ((red q).run.run s) = (game q).run.run s) {α : Type}
    (oa : OracleComp spec₁ α) (s : σ) :
    simulateQ impl ((simulateQ red oa).run.run s) = (simulateQ game oa).run.run s := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure x => simp
  | query_bind t f ih =>
    simp only [simulateQ_bind, WriterT.run_bind, simulateQ_spec_query, StateT.run_bind,
      StateT.run_map, bridge t, simulateQ_map]
    exact bind_congr fun p => by rw [ih p.1.1 p.2]

/-- Relabelling commutes with additive cost instrumentation for any cost on the shared query
domain `ℕ ⊕ Bytes`: each query is relabelled into exactly one query with the same input. -/
theorem simulateQ_relabel_run_addCost {ω : Type} [AddCommMonoid ω] (e : A ≃ B)
    (cost : ℕ ⊕ Bytes → ω) {α : Type} (P : OracleComp (Game.World A) α) :
    simulateQ (relabel e) (simulateQ (addCostOracle (spec := Game.World A) cost) P).run =
      (simulateQ (addCostOracle (spec := Game.World B) cost)
        (simulateQ (relabel e) P)).run := by
  rw [← QueryImpl.simulateQ_compose]
  refine simulateQ_writerT_run_compose _ _ _ (fun t => ?_) P
  rcases t with n | x <;> simp [addCostOracle]

/-- The hash cost does not depend on the answer type. -/
theorem hashCost_eq :
    (Game.hashCost (Output := A) : ℕ ⊕ Bytes → ℕ) = Game.hashCost (Output := B) := by
  funext t
  rcases t with n | x <;> rfl

/-- Relabelling commutes with counting all hash calls. -/
theorem simulateQ_relabel_countAllHashes (e : A ≃ B) {α : Type}
    (P : OracleComp (Game.World A) α) :
    simulateQ (relabel e) (Game.countAllHashes P) =
      Game.countAllHashes (simulateQ (relabel e) P) := by
  unfold Game.countAllHashes
  rw [simulateQ_map, simulateQ_relabel_run_addCost, hashCost_eq]

/-- Relabelling commutes with counting queries by any cost on `ℕ ⊕ Bytes`. -/
theorem simulateQ_relabel_countQueries (e : A ≃ B) (cost : ℕ ⊕ Bytes → Game.Counts)
    {α : Type} (P : OracleComp (Game.World A) α) :
    simulateQ (relabel e) (Game.countQueries cost P) =
      Game.countQueries cost (simulateQ (relabel e) P) := by
  unfold Game.countQueries
  rw [simulateQ_map, simulateQ_relabel_run_addCost]

/-! ## Bridged schemes -/

/-- A bridge from a scheme with hash answers in `A` to one with hash answers in `B` along
`e : A ≃ B`: key maps under which signing and verification agree through `relabel e`, and key
generations that, counted and followed by any continuation, have the same law in the
random-oracle model. -/
structure SchemeBridge (e : A ≃ B) [SampleableType B] {PKA SKA PKB SKB : Type}
    (SA : Game.ExternalScheme A PKA SKA) (SB : Game.ExternalScheme B PKB SKB) where
  /-- The public key of the `B` scheme corresponding to one of the `A` scheme. -/
  pk : PKA → PKB
  /-- The secret key of the `B` scheme corresponding to one of the `A` scheme. -/
  sk : SKA → SKB
  /-- Relabelled signing is signing with the corresponding key. -/
  sign : ∀ s req, simulateQ (relabel e) (SA.sign s req) = SB.sign (sk s) req
  /-- Relabelled verification is verification with the corresponding key. -/
  verify : ∀ p req sig, simulateQ (relabel e) (SA.verify p req sig) = SB.verify (pk p) req sig
  /-- Relabelled key generation, with its keys mapped and its hash calls counted, followed by any
  continuation, has the law of the `B` scheme's key generation followed by that continuation. -/
  keygen : ∀ {γ : Type} (k : SKB × PKB → ℕ → OracleComp (Game.World B) γ),
    Xmss.RandomOracleModel.run (Game.countAllHashes (simulateQ (relabel e) SA.keygen) >>=
        fun r => k (sk r.1.1, pk r.1.2) r.2) =ᵈ
      Xmss.RandomOracleModel.run (Game.countAllHashes SB.keygen >>= fun r => k r.1 r.2)

/-- Counting the hash calls of a mapped program maps the output of the counted program. -/
theorem countAllHashes_map {Output α β : Type} (f : α → β)
    (P : OracleComp (Game.World Output) α) :
    Game.countAllHashes (f <$> P) = Prod.map f id <$> Game.countAllHashes P := by
  simp [Game.countAllHashes, Functor.map_map]

/-- The key-generation field of a `SchemeBridge` holds when relabelled key generation, with its
keys mapped, is the `B` scheme's key generation. -/
theorem keygen_of_map_eq [SampleableType B] {e : A ≃ B} {PKA SKA PKB SKB : Type}
    {SA : Game.ExternalScheme A PKA SKA} {SB : Game.ExternalScheme B PKB SKB}
    (pk : PKA → PKB) (sk : SKA → SKB)
    (h : Prod.map sk pk <$> simulateQ (relabel e) SA.keygen = SB.keygen)
    {γ : Type} (k : SKB × PKB → ℕ → OracleComp (Game.World B) γ) :
    Xmss.RandomOracleModel.run (Game.countAllHashes (simulateQ (relabel e) SA.keygen) >>=
        fun r => k (sk r.1.1, pk r.1.2) r.2) =ᵈ
      Xmss.RandomOracleModel.run (Game.countAllHashes SB.keygen >>= fun r => k r.1 r.2) := by
  rw [← h, countAllHashes_map, bind_map_left]
  rfl

/-! ## Key generations that draw their seeds first -/

/-- A uniform query lifted from `unifSpec` is the uniform query of the world. -/
theorem liftM_unifSpec_query {Output : Type} (t : ℕ) :
    (liftM (unifSpec.query t) : OracleComp (Game.World Output) _) =
      liftM ((Game.World Output).query (.inl t)) := rfl

/-- Uniform draws cost nothing when hash calls are counted. -/
theorem run_simulateQ_addCostOracle_liftM {Output α : Type} (oa : ProbComp α) :
    (simulateQ (addCostOracle (spec := Game.World Output) Game.hashCost)
      (liftM oa : OracleComp (Game.World Output) α)).run =
      (fun a => (a, 1)) <$> (liftM oa : OracleComp (Game.World Output) α) := by
  rw [← liftComp_eq_liftM, liftComp_def]
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, WriterT.run_bind, ih, map_bind]
    simp only [simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map,
      liftM_unifSpec_query]
    simp [addCostOracle, QueryImpl.withAddCost, Game.hashCost, Xmss.RandomOracleModel.hashCost]

/-- Counting the hash calls of a program that begins with a uniform draw counts those of its
continuation. -/
theorem countAllHashes_liftM_bind {Output α β : Type} (oa : ProbComp α)
    (f : α → OracleComp (Game.World Output) β) :
    Game.countAllHashes ((liftM oa : OracleComp (Game.World Output) α) >>= f) =
      (liftM oa : OracleComp (Game.World Output) α) >>= fun a => Game.countAllHashes (f a) := by
  simp only [Game.countAllHashes, simulateQ_bind, WriterT.run_bind,
    run_simulateQ_addCostOracle_liftM, bind_map_left, map_bind, Functor.map_map, one_mul]

/-- In the random-oracle model, a uniform draw at the start of a program is the draw itself,
followed by the run of the continuation from the empty cache. -/
theorem run_liftM_bind {Output α β : Type} [SampleableType Output] (oa : ProbComp α)
    (f : α → OracleComp (Game.World Output) β) :
    Xmss.RandomOracleModel.run ((liftM oa : OracleComp (Game.World Output) α) >>= f) =
      oa >>= fun a => Xmss.RandomOracleModel.run (f a) := by
  simp only [Xmss.RandomOracleModel.run, Xmss.RandomOracleModel.impl, simulateQ_bind,
    QueryImpl.simulateQ_add_liftM_left, StateT.run'_eq, StateT.run_bind,
    unifFwdImpl.simulateQ_run, bind_map_left, map_bind]

/-- The key-generation field of a `SchemeBridge` holds when both key generations first draw their
seeds, relabelled key generation from `sA` and continuing with `G`, the `B` scheme's from `sB` and
continuing with `H`, when `φ` carries the law of `sA` to that of `sB`, and when `G x` with its keys
mapped is `H (φ x)`. -/
theorem keygen_of_seeds [SampleableType B] {e : A ≃ B} {PKA SKA PKB SKB : Type}
    {SA : Game.ExternalScheme A PKA SKA} {SB : Game.ExternalScheme B PKB SKB}
    (pk : PKA → PKB) (sk : SKA → SKB) {X Y : Type} (sA : ProbComp X) (sB : ProbComp Y)
    (φ : X → Y) (hφ : φ <$> sA =ᵈ sB)
    (G : X → OracleComp (Game.World B) (SKA × PKA))
    (H : Y → OracleComp (Game.World B) (SKB × PKB))
    (hA : simulateQ (relabel e) SA.keygen = (liftM sA : OracleComp (Game.World B) X) >>= G)
    (hB : SB.keygen = (liftM sB : OracleComp (Game.World B) Y) >>= H)
    (hGH : ∀ x, Prod.map sk pk <$> G x = H (φ x))
    {γ : Type} (k : SKB × PKB → ℕ → OracleComp (Game.World B) γ) :
    Xmss.RandomOracleModel.run (Game.countAllHashes (simulateQ (relabel e) SA.keygen) >>=
        fun r => k (sk r.1.1, pk r.1.2) r.2) =ᵈ
      Xmss.RandomOracleModel.run (Game.countAllHashes SB.keygen >>= fun r => k r.1 r.2) := by
  rw [hA, hB, countAllHashes_liftM_bind, countAllHashes_liftM_bind, bind_assoc, bind_assoc,
    run_liftM_bind, run_liftM_bind]
  have hx : ∀ x, Xmss.RandomOracleModel.run (Game.countAllHashes (G x) >>=
      fun r => k (sk r.1.1, pk r.1.2) r.2) =
      Xmss.RandomOracleModel.run (Game.countAllHashes (H (φ x)) >>= fun r => k r.1 r.2) := by
    intro x
    rw [← hGH, countAllHashes_map, bind_map_left]
    rfl
  simp only [hx]
  rw [← bind_map_left φ sA (fun y => Xmss.RandomOracleModel.run
    (Game.countAllHashes (H y) >>= fun r => k r.1 r.2))]
  exact hφ.bind fun _ => EvalDistEq.rfl

/-- Answer a query of the `B` world and signing oracle in the `A` world and signing oracle:
world queries are unlabelled, signing requests pass through. -/
@[expose] def unlabelAdversary (e : A ≃ B) :
    QueryImpl (Game.World B + Game.SigningSpec) (OracleComp (Game.World A + Game.SigningSpec))
  | .inl (.inl n) => liftM ((Game.World A + Game.SigningSpec).query (.inl (.inl n)))
  | .inl (.inr x) => e <$> liftM ((Game.World A + Game.SigningSpec).query (.inl (.inr x)))
  | .inr req => liftM ((Game.World A + Game.SigningSpec).query (.inr req))

/-- Lifting an oracle computation into a writer over a state pairs each output with the unit
log and the unchanged state. -/
theorem run_run_liftM {ι : Type} {spec : OracleSpec ι} {ω σ α : Type} [Monoid ω]
    (x : OracleComp spec α) (s : σ) :
    (liftM x : WriterT ω (StateT σ (OracleComp spec)) α).run.run s =
      (fun a => ((a, 1), s)) <$> x := by
  simp [liftM, monadLift, MonadLift.monadLift, StateT.run_lift]

/-- Modifying the state of a writer over a state logs nothing and applies the modification. -/
theorem run_run_modify {ι : Type} {spec : OracleSpec ι} {ω σ : Type} [Monoid ω]
    (f : σ → σ) (s : σ) :
    (WriterT.run (modify f : WriterT ω (StateT σ (OracleComp spec)) PUnit)).run s =
      pure ((⟨⟩, 1), f s) := by
  simp [modify, modifyGet, MonadStateOf.modifyGet, StateT.run]
  rfl

variable {PKA SKA PKB SKB : Type}

/-- What follows key generation in the experiment counted by source, given the keys and key
generation's hash count. -/
@[expose] noncomputable def afterKeygenBySource (scheme : Game.ExternalScheme B PKB SKB)
    (adversary : Game.Adversary B PKB) (keys : SKB × PKB) (keygenHashes : ℕ) :
    OracleComp (Game.World B) (Game.Outcome × Xmss.Unforgeability.QueryCounts) := do
  let (outcome, laterHashes) ← Game.countAllHashes (Game.afterKeygen scheme adversary keys)
  return (outcome, Game.sourceCounts outcome keygenHashes laterHashes)

/-- The experiment counted by source is key generation, counted, followed by
`afterKeygenBySource`. -/
theorem experimentBySource_eq (scheme : Game.ExternalScheme B PKB SKB)
    (adversary : Game.Adversary B PKB) :
    Game.experimentBySource scheme adversary =
      Game.countAllHashes scheme.keygen >>= fun r =>
        afterKeygenBySource scheme adversary r.1 r.2 := rfl

variable {e : A ≃ B} [SampleableType B]
  {SA : Game.ExternalScheme A PKA SKA} {SB : Game.ExternalScheme B PKB SKB}

/-- The adversary against the `A` scheme that runs `adversary` on the corresponding public key,
unlabelling its hash queries and forwarding its signing requests. -/
@[expose] def adapt (b : SchemeBridge e SA SB) (adversary : Game.Adversary B PKB) :
    Game.Adversary A PKA where
  main pk := simulateQ (unlabelAdversary e) (adversary.main (b.pk pk))

/-- The relabelled adversary's phase of the adapted adversary against the `A` scheme is the
adversary's phase against the `B` scheme, with the corresponding keys. -/
theorem simulateQ_relabel_adversaryPhase (b : SchemeBridge e SA SB)
    (adversary : Game.Adversary B PKB) (sk : SKA) (pk : PKA) (s : Game.SigningLog) :
    simulateQ (relabel e) ((simulateQ
      ((QueryImpl.ofLift (Game.World A)
          (StateT Game.SigningLog (OracleComp (Game.World A)))).withAddCost
          (fun input => Game.Counts.single .hash (Game.hashCost input)) +
        Game.signingOracle SA sk)
      ((adapt b adversary).main pk)).run.run s) =
    (simulateQ
      ((QueryImpl.ofLift (Game.World B)
          (StateT Game.SigningLog (OracleComp (Game.World B)))).withAddCost
          (fun input => Game.Counts.single .hash (Game.hashCost input)) +
        Game.signingOracle SB (b.sk sk))
      (adversary.main (b.pk pk))).run.run s := by
  simp only [adapt]
  rw [← QueryImpl.simulateQ_compose]
  refine simulateQ_writerT_stateT_run_compose _ _ _ (fun q s => ?_) _ s
  rcases q with (n | x) | req
  · simp [unlabelAdversary]
    rfl
  · simp [unlabelAdversary]
    rfl
  · simp [unlabelAdversary, Game.signingOracle, run_run_liftM, run_run_modify, b.sign]

/-- Relabelling the adapted adversary's phase and verification, after keys `(sk, pk)` of the `A`
scheme, gives the adversary's phase and verification against the `B` scheme with the
corresponding keys. -/
theorem simulateQ_relabel_afterKeygen (b : SchemeBridge e SA SB)
    (adversary : Game.Adversary B PKB) (sk : SKA) (pk : PKA) :
    simulateQ (relabel e) (Game.afterKeygen SA (adapt b adversary) (sk, pk)) =
      Game.afterKeygen SB adversary (b.sk sk, b.pk pk) := by
  simp only [Game.afterKeygen, simulateQ_bind]
  rw [simulateQ_relabel_adversaryPhase b adversary sk pk []]
  refine bind_congr fun r => ?_
  rcases r with ⟨⟨forgery, counts⟩, signed⟩
  simp only [simulateQ_pure]
  rw [simulateQ_relabel_countQueries, b.verify, hashCost_eq]

/-- The relabelled experiment of the adapted adversary is the relabelled key generation of the
`A` scheme, counted, with its keys mapped, followed by the rest of the `B` experiment. -/
theorem simulateQ_relabel_experimentBySource (b : SchemeBridge e SA SB)
    (adversary : Game.Adversary B PKB) :
    simulateQ (relabel e) (Game.experimentBySource SA (adapt b adversary)) =
      Game.countAllHashes (simulateQ (relabel e) SA.keygen) >>= fun r =>
        afterKeygenBySource SB adversary (b.sk r.1.1, b.pk r.1.2) r.2 := by
  simp only [Game.experimentBySource, simulateQ_bind]
  rw [simulateQ_relabel_countAllHashes]
  refine bind_congr fun r => ?_
  rcases r with ⟨⟨sk, pk⟩, keygenHashes⟩
  simp only [simulateQ_pure, simulateQ_relabel_countAllHashes, simulateQ_relabel_afterKeygen,
    afterKeygenBySource]

variable [SampleableType A]

/-- The run counted by source of an adversary against the `B` scheme has the law of the run of
the adapted adversary against the `A` scheme. -/
theorem runBySource_evalDistEq (b : SchemeBridge e SA SB)
    (he : (e <$> ($ᵗ A : ProbComp A)) =ᵈ ($ᵗ B : ProbComp B))
    (adversary : Game.Adversary B PKB) :
    Game.runBySource SB adversary =ᵈ Game.runBySource SA (adapt b adversary) := by
  calc Game.runBySource SB adversary
      = Xmss.RandomOracleModel.run (Game.countAllHashes SB.keygen >>= fun r =>
          afterKeygenBySource SB adversary r.1 r.2) := rfl
    _ =ᵈ Xmss.RandomOracleModel.run (Game.countAllHashes (simulateQ (relabel e) SA.keygen) >>=
          fun r => afterKeygenBySource SB adversary (b.sk r.1.1, b.pk r.1.2) r.2) :=
        (b.keygen _).symm
    _ = Xmss.RandomOracleModel.run
          (simulateQ (relabel e) (Game.experimentBySource SA (adapt b adversary))) := by
        rw [simulateQ_relabel_experimentBySource]
    _ =ᵈ Game.runBySource SA (adapt b adversary) := run_simulateQ_relabel e he _

/-- The security experiment of an adversary against the `B` scheme has the law of that of the
adapted adversary against the `A` scheme. -/
theorem experiment_evalDistEq (b : SchemeBridge e SA SB)
    (he : (e <$> ($ᵗ A : ProbComp A)) =ᵈ ($ᵗ B : ProbComp B))
    (adversary : Game.Adversary B PKB) :
    (Game.securityGame SB).experiment () adversary =ᵈ
      (Game.securityGame SA).experiment () (adapt b adversary) :=
  (runBySource_evalDistEq b he adversary).map _

/-- **Security bits transfer along a bridge.** If `e` carries the uniform sampler of `A` to that
of `B` and the two schemes are bridged along `e`, every security bit of the `A` scheme is one of
the `B` scheme, in every counting mode. -/
theorem hasSecurityBits_of_bridge (b : SchemeBridge e SA SB)
    (he : (e <$> ($ᵗ A : ProbComp A)) =ᵈ ($ᵗ B : ProbComp B))
    {Z : Finset Xmss.Unforgeability.QueryKind} {bits : ℕ}
    (h : Game.HasSecurityBits SA Z bits) : Game.HasSecurityBits SB Z bits := by
  intro q hq adversary hlimit hbound
  have hE := experiment_evalDistEq b he adversary
  have hadv : (Game.securityGame SB).advantage () adversary =
      (Game.securityGame SA).advantage () (adapt b adversary) := hE.prEvent_eq _
  rw [hadv]
  refine h q hq (adapt b adversary) ?_ ?_
  · exact (hE.prEvent_eq _).symm.trans hlimit
  · exact (hE.prEvent_eq _).symm.trans hbound

end SlhDsaSecurity.Bridge
