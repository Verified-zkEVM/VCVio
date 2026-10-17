/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import VCVio.CryptoFoundations.SignatureAlg.RomQueryCount
public import VCVio.OracleComp.QueryTracking.RandomOracle.Encoded

/-!
# Routed adversaries

A signature scheme in the random oracle model runs over `unifSpec + hs`, private sampling and
typed hash oracles `hs`. An adversary may instead hold raw oracles `ext`, which a router reads as
typed queries. Both live on the common interface `unifSpec + (hs + ext)`: the scheme through
`OracleComp.liftTypedImpl`, an adversary over `unifSpec + ext` through `OracleComp.liftRawImpl`.

A router `R : QueryImpl ext (StateT σ (OracleComp (unifSpec + hs)))` answers a raw query from a
private state `σ` and queries of `unifSpec + hs`. It can be held in two places.

* By the handler: `OracleComp.handlerRouterImpl ro R` answers the common interface on the pair of
  the state of a handler `ro` of `unifSpec + hs` and the router's state, running `R` at raw
  queries.
* By the program: `OracleComp.programRouterImpl R` answers raw queries by `R` on a state the
  program itself holds. `SignatureAlg.UnforgeableAdversary.route R s₀ adv` runs `adv` so, with
  `R pk` at its public key `pk` from the router state `s₀`; it is an adversary against the scheme
  over `unifSpec + hs`.

The two agree on the unforgeability experiment
(`SignatureAlg.map_run_simulateQ_handlerRouterImpl_unforgeableTranscriptExperiment`): the
transcript and the state of `ro` of the experiment on the common interface under the
handler-held router are those of the experiment of the scheme against the routed adversary under
`ro`. The proof runs the router through the logging layer of the signing oracle
(`OracleComp.simulateQ_handlerRouterImpl_run_simulateQ_passthrough_add_withLogging`). A router
reading the public key agrees with a fixed router at every key the key generation can output
(`SignatureAlg.map_run_simulateQ_handlerRouterImpl_unforgeableTranscriptExperiment_evalDistEq`).
A router making at most one hash query per raw query keeps the adversary's budget
(`SignatureAlg.UnforgeableAdversary.RomQueryBound.route`).

For an encoding of typed random oracles into one random oracle
(`OracleComp.RandomOracleEncoding`), the typed world is the handler-held router of the random
oracle model of `hs` and the router `RandomOracleEncoding.tableRouter`, which keeps the table of
private values in its state (`RandomOracleEncoding.typedImpl_eq_handlerRouterImpl`). The
experiment against an adversary over the single oracle is then bounded by the experiment against
the routed adversary in the random oracle model of the typed oracles, or a clash
(`RandomOracleEncoding.prEvent_simulateQ_romImpl_run_unforgeableTranscriptExperiment_le`).
-/

public section

open OracleSpec OracleComp

namespace OracleComp

variable {ι ιe ιs : Type} {hs : OracleSpec ι} {ext : OracleSpec ιe} {sig : OracleSpec ιs}
  {σ τ : Type}

/-! ## The common interface and the router -/

/-- The queries of a program over `unifSpec + hs` as queries of `unifSpec + (hs + ext)`. -/
@[expose] def liftTypedImpl : QueryImpl (unifSpec + hs) (OracleComp (unifSpec + (hs + ext)))
  | .inl n => (query (spec := unifSpec + (hs + ext)) (.inl n) : OracleComp _ (Fin (n + 1)))
  | .inr t => (query (spec := unifSpec + (hs + ext)) (.inr (.inl t)) : OracleComp _ (hs.Range t))

/-- The queries of a program over `unifSpec + ext` as queries of `unifSpec + (hs + ext)`. -/
@[expose] def liftRawImpl : QueryImpl (unifSpec + ext) (OracleComp (unifSpec + (hs + ext)))
  | .inl n => (query (spec := unifSpec + (hs + ext)) (.inl n) : OracleComp _ (Fin (n + 1)))
  | .inr x =>
      (query (spec := unifSpec + (hs + ext)) (.inr (.inr x)) : OracleComp _ (ext.Range x))

/-- The queries of a program over `unifSpec + hs` as queries of `(unifSpec + hs) + sig`, along the
left summand. -/
@[expose] def liftAmbientImpl :
    QueryImpl (unifSpec + hs) (OracleComp ((unifSpec + hs) + sig)) := fun t =>
  (query (spec := (unifSpec + hs) + sig) (.inl t) :
    OracleComp ((unifSpec + hs) + sig) ((unifSpec + hs).Range t))

/-- Lifting the queries of a program over `unifSpec + hs` to the common interface is its lift
along the inclusion of `unifSpec + hs` in `unifSpec + (hs + ext)`. -/
theorem simulateQ_liftTypedImpl {α : Type} (oa : OracleComp (unifSpec + hs) α) :
    simulateQ (liftTypedImpl (ext := ext)) oa = liftComp oa (unifSpec + (hs + ext)) := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    rcases t with n | t <;> simp [liftTypedImpl, ih] <;> rfl

/-- Lifting the queries of a program over `unifSpec + ext` to the common interface is its lift
along the inclusion of `unifSpec + ext` in `unifSpec + (hs + ext)`. -/
theorem simulateQ_liftRawImpl {α : Type} (oa : OracleComp (unifSpec + ext) α) :
    simulateQ (liftRawImpl (hs := hs)) oa = liftComp oa (unifSpec + (hs + ext)) := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    rcases t with n | t <;> simp [liftRawImpl, ih] <;> rfl

/-- Lifting the queries of a program over `unifSpec + hs` along the left summand is its lift along
the inclusion of `unifSpec + hs` in `(unifSpec + hs) + sig`. -/
theorem simulateQ_liftAmbientImpl {α : Type} (oa : OracleComp (unifSpec + hs) α) :
    simulateQ (liftAmbientImpl (sig := sig)) oa = liftComp oa ((unifSpec + hs) + sig) := by
  rw [liftComp_def]
  congr 1
  funext t
  rcases t with n | t <;> rfl

/-- The router held by the program: a raw query `x` is answered by `R x` on the router's state,
and every other query is passed on. The router's queries are lifted to `(unifSpec + hs) + sig`
along the left summand. -/
@[expose] def programRouterImpl (R : QueryImpl ext (StateT σ (OracleComp (unifSpec + hs)))) :
    QueryImpl ((unifSpec + (hs + ext)) + sig) (StateT σ (OracleComp ((unifSpec + hs) + sig)))
  | .inl (.inl n) =>
      (liftM (query (spec := (unifSpec + hs) + sig) (.inl (.inl n)) :
        OracleComp ((unifSpec + hs) + sig) (Fin (n + 1))) :
        StateT σ (OracleComp ((unifSpec + hs) + sig)) _)
  | .inl (.inr (.inl t)) =>
      (liftM (query (spec := (unifSpec + hs) + sig) (.inl (.inr t)) :
        OracleComp ((unifSpec + hs) + sig) (hs.Range t)) :
        StateT σ (OracleComp ((unifSpec + hs) + sig)) _)
  | .inl (.inr (.inr x)) => StateT.mk fun s => simulateQ liftAmbientImpl ((R x).run s)
  | .inr m =>
      (liftM (query (spec := (unifSpec + hs) + sig) (.inr m) :
        OracleComp ((unifSpec + hs) + sig) (sig.Range m)) :
        StateT σ (OracleComp ((unifSpec + hs) + sig)) _)

/-- The router held by the handler: a query of `unifSpec + hs` is answered by `ro` on the first
component of the state, and a raw query `x` runs `R x` on the second component, its own queries
answered by `ro` on the first. -/
@[expose] def handlerRouterImpl (ro : QueryImpl (unifSpec + hs) (StateT τ ProbComp))
    (R : QueryImpl ext (StateT σ (OracleComp (unifSpec + hs)))) :
    QueryImpl (unifSpec + (hs + ext)) (StateT (τ × σ) ProbComp)
  | .inl n => StateT.mk fun p => (fun z => (z.1, (z.2, p.2))) <$> (ro (.inl n)).run p.1
  | .inr (.inl t) => StateT.mk fun p => (fun z => (z.1, (z.2, p.2))) <$> (ro (.inr t)).run p.1
  | .inr (.inr x) => StateT.mk fun p =>
      (fun z => (z.1.1, (z.2, z.1.2))) <$> (simulateQ ro ((R x).run p.2)).run p.1

/-- A probabilistic computation lifted to `unifSpec + hs` makes no query to `hs`. -/
theorem isQueryBoundP_liftM_isRight {α : Type} (oa : ProbComp α) :
    IsQueryBoundP (liftM oa : OracleComp (unifSpec + hs) α) (fun t => t.isRight) 0 := by
  induction oa using OracleComp.inductionOn with
  | pure a => trivial
  | query_bind n k ih =>
    simp only [liftM_bind]
    exact isQueryBoundP_bind_zero _ _
      ((isQueryBoundP_query_iff (spec := unifSpec + hs) _ (.inl n) 0).2 fun h => by
        simp at h) ih

/-- At a raw query, the router held by the program makes, on `(unifSpec + hs) + sig`, the queries
of the router lifted along the left summand. -/
theorem isQueryBoundP_run_programRouterImpl_inr_inr
    {R : QueryImpl ext (StateT σ (OracleComp (unifSpec + hs)))}
    {q : ((unifSpec + hs) + sig).Domain → Prop} [DecidablePred q] {n : ℕ} (x : ιe) (s : σ)
    (h : IsQueryBoundP ((R x).run s) (fun t => q (.inl t)) n) :
    IsQueryBoundP ((programRouterImpl (sig := sig) R (.inl (.inr (.inr x)))).run s) q n := by
  simp only [programRouterImpl, StateT.run_mk]
  refine h.simulateQ_of_step (fun t _ => ?_) fun t ht => ?_
  · exact (isQueryBoundP_query_iff (spec := (unifSpec + hs) + sig) q (.inl t) 1).2
      fun _ => Nat.one_pos
  · exact (isQueryBoundP_query_iff (spec := (unifSpec + hs) + sig) q (.inl t) 0).2
      fun h => (ht h).elim

/-! ## Internalising the router -/

variable (ro : QueryImpl (unifSpec + hs) (StateT τ ProbComp))
  (R : QueryImpl ext (StateT σ (OracleComp (unifSpec + hs))))

/-- A program over `unifSpec + hs`, lifted to the common interface, runs under the handler-held
router as under `ro`, with the router's state untouched. -/
theorem simulateQ_handlerRouterImpl_simulateQ_liftTypedImpl_run {α : Type}
    (oa : OracleComp (unifSpec + hs) α) (c : τ) (s : σ) :
    (simulateQ (handlerRouterImpl ro R) (simulateQ (liftTypedImpl (ext := ext)) oa)).run (c, s) =
      (fun z => (z.1, (z.2, s))) <$> (simulateQ ro oa).run c := by
  induction oa using OracleComp.inductionOn generalizing c with
  | pure a => simp
  | query_bind t k ih =>
    rcases t with n | t <;> simp [liftTypedImpl, handlerRouterImpl, ih]

/-- A logged handler of `sig`, with the queries of `unifSpec + hs` passed on, runs a program over
`unifSpec + hs` lifted along the left summand as the program itself, with an empty log. -/
theorem run_simulateQ_passthrough_add_withLogging_simulateQ_liftAmbientImpl
    (f : QueryImpl sig (OracleComp (unifSpec + hs))) {α : Type}
    (oa : OracleComp (unifSpec + hs) α) :
    (simulateQ ((unifSpec + hs).passthrough + f.withLogging)
      (simulateQ liftAmbientImpl oa)).run = (fun a => (a, [])) <$> oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind q k ih =>
    simp only [OracleSpec.passthrough, QueryImpl.passthrough_add] at ih ⊢
    simp [liftAmbientImpl, ih]

/-- **Internalising a router through a logged signing layer.** Let `oa` be a program on the
common interface with a signing oracle `sig`, answered by the logged handler `f` of the scheme
over `unifSpec + hs`. Run under the handler-held router, with the signing handler lifted to the
common interface, `oa` has the output, log and state of `ro` of the program that holds the router
in its own state, answered by `f` and run under `ro`; the router's final state is the second
component of the handler's state. -/
theorem simulateQ_handlerRouterImpl_run_simulateQ_passthrough_add_withLogging
    (f : QueryImpl sig (OracleComp (unifSpec + hs))) {α : Type}
    (oa : OracleComp ((unifSpec + (hs + ext)) + sig) α) (c : τ) (s : σ) :
    (simulateQ (handlerRouterImpl ro R)
        (simulateQ ((unifSpec + (hs + ext)).passthrough +
            QueryImpl.withLogging (fun m => simulateQ (liftTypedImpl (ext := ext)) (f m) :
              QueryImpl sig (OracleComp (unifSpec + (hs + ext))))) oa).run).run (c, s) =
      (fun z => ((z.1.1.1, z.1.2), (z.2, z.1.1.2))) <$>
        (simulateQ ro (simulateQ ((unifSpec + hs).passthrough + f.withLogging)
          ((simulateQ (programRouterImpl R) oa).run s)).run).run c := by
  induction oa using OracleComp.inductionOn generalizing c s with
  | pure a => simp
  | query_bind t k ih =>
    have hC := @run_simulateQ_passthrough_add_withLogging_simulateQ_liftAmbientImpl _ _ _ _ f
    simp only [OracleSpec.passthrough, QueryImpl.passthrough_add] at ih hC
    rcases t with (n | t | x) | m
    pick_goal 4
    · simp only [QueryImpl.passthrough_add, add_apply_inr, simulateQ_bind, simulateQ_query,
        OracleQuery.input_query, OracleQuery.cont_query, QueryImpl.add_apply_inr,
        QueryImpl.withLogging_apply, bind_pure_comp, map_bind, Functor.map_map, id_eq, bind_assoc,
        bind_map_left, WriterT.run_bind, WriterT.run_liftM, List.empty_eq, WriterT.run_tell,
        pure_bind, List.cons_append, List.nil_append, simulateQ_map, StateT.run_bind,
        simulateQ_handlerRouterImpl_simulateQ_liftTypedImpl_run, StateT.run_map, programRouterImpl,
        HasQuery.instOfMonadLift_query, id_map, StateT.run_monadLift, monadLift_self]
      refine bind_congr fun a => ?_
      rw [ih a.1 a.2 s]
      simp
    all_goals
      simp only [QueryImpl.passthrough_add, add_apply_inl, add_apply_inr, simulateQ_bind,
        simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, QueryImpl.add_apply_inl,
        PFunctor.Handler.liftTarget_apply, ofPFunctor_toPFunctor, QueryImpl.id'_apply, id_map,
        WriterT.run_bind, WriterT.run_liftM, List.empty_eq, bind_map_left, List.nil_append,
        Prod.mk.eta, id_map', handlerRouterImpl, StateT.run_bind, StateT.run_mk, programRouterImpl,
        HasQuery.instOfMonadLift_query, StateT.run_monadLift, monadLift_self, bind_pure_comp,
        hC, map_bind]
      first
      | exact bind_congr fun a => ih a.1 a.2 s
      | exact bind_congr fun a => ih a.1.1 a.2 a.1.2

end OracleComp

namespace SignatureAlg

variable {ι ιe : Type} {hs : OracleSpec ι} {ext : OracleSpec ιe} {M PK SK SK' S σ τ : Type}

/-! ## The routed adversary -/

/-- The adversary that runs `adv`, an adversary on the common interface `unifSpec + (hs + ext)`,
with its raw queries answered by the router `R pk` at its public key `pk`, from the router state
`s₀` held in its own state. It is an adversary against any scheme over `unifSpec + hs` with the
same messages, public keys and signatures. -/
@[expose] def UnforgeableAdversary.route
    {sigAlg' : SignatureAlg (OracleComp (unifSpec + (hs + ext))) M PK SK' S}
    {sigAlg : SignatureAlg (OracleComp (unifSpec + hs)) M PK SK S}
    (R : PK → QueryImpl ext (StateT σ (OracleComp (unifSpec + hs)))) (s₀ : σ)
    (adv : UnforgeableAdversary sigAlg') : UnforgeableAdversary sigAlg where
  main pk := (simulateQ (programRouterImpl (R pk)) (adv.main pk)).run' s₀

/-- **Internalising a router in the unforgeability experiment.** The experiment of a scheme over
`unifSpec + hs`, lifted to the common interface, against an adversary on the common interface,
run under the handler-held router of `ro` and `R` from `(c, s)`, has as transcript and state of
`ro` the run under `ro` from `c` of the experiment of the scheme against the adversary that holds
`R` from `s`. -/
theorem map_run_simulateQ_handlerRouterImpl_unforgeableTranscriptExperiment
    (ro : QueryImpl (unifSpec + hs) (StateT τ ProbComp))
    (R : QueryImpl ext (StateT σ (OracleComp (unifSpec + hs))))
    {sigAlg : SignatureAlg (OracleComp (unifSpec + hs)) M PK SK S}
    (adv : UnforgeableAdversary (sigAlg.map (simulateQ' (liftTypedImpl (ext := ext)))))
    (c : τ) (s : σ) :
    Prod.map id Prod.fst <$>
        (simulateQ (handlerRouterImpl ro R) (unforgeableTranscriptExperiment adv)).run (c, s) =
      (simulateQ ro (unforgeableTranscriptExperiment (sigAlg := sigAlg)
        (adv.route (fun _ => R) s))).run c := by
  simp only [unforgeableTranscriptExperiment_def, runWithSigningOracle, simulateQ_bind,
    StateT.run_bind, map_keygen, map_verify,
    simulateQ_handlerRouterImpl_simulateQ_liftTypedImpl_run, map_bind, bind_map_left]
  refine bind_congr fun a => ?_
  have hsign : (sigAlg.map (simulateQ' (liftTypedImpl (ext := ext)))).signingOracle a.1.1 a.1.2 =
      QueryImpl.withLogging (fun m => simulateQ (liftTypedImpl (ext := ext))
        (sigAlg.sign a.1.1 a.1.2 m) : QueryImpl (M →ₒ S) (OracleComp (unifSpec + (hs + ext)))) :=
    rfl
  rw [hsign, simulateQ_handlerRouterImpl_run_simulateQ_passthrough_add_withLogging]
  simp [UnforgeableAdversary.route, signingOracle, StateT.run'_eq,
    simulateQ_handlerRouterImpl_simulateQ_liftTypedImpl_run]

/-- Routers that agree at every public key the key generation can output give routed adversaries
whose experiments have equal measures under any handler `ro`. -/
theorem run_simulateQ_unforgeableTranscriptExperiment_route_congr
    (ro : QueryImpl (unifSpec + hs) (StateT τ ProbComp))
    {sigAlg : SignatureAlg (OracleComp (unifSpec + hs)) M PK SK S}
    {sigAlg' : SignatureAlg (OracleComp (unifSpec + (hs + ext))) M PK SK' S}
    (adv : UnforgeableAdversary sigAlg')
    {R R' : PK → QueryImpl ext (StateT σ (OracleComp (unifSpec + hs)))}
    (h : ∀ z ∈ support sigAlg.keygen, R z.1 = R' z.1) (s : σ) (c : τ) :
    (simulateQ ro (unforgeableTranscriptExperiment (sigAlg := sigAlg) (adv.route R s))).run c =ᵈ
      (simulateQ ro
        (unforgeableTranscriptExperiment (sigAlg := sigAlg) (adv.route R' s))).run c := by
  simp only [unforgeableTranscriptExperiment_def, simulateQ_bind, StateT.run_bind]
  refine EvalDistEq.bind_congr_of_support _ fun z hz => ?_
  have hk : z.1 ∈ support sigAlg.keygen :=
    support_simulateQ_run'_subset ro sigAlg.keygen c (by
      rw [StateT.run'_eq, MonadAttach.support_map]; exact Set.mem_image_of_mem _ hz)
  simp only [UnforgeableAdversary.route, h z.1 hk]
  exact EvalDistEq.refl _

/-- **Internalising a router that reads the public key.** If the router `R pk` is `R₀` at every
public key the key generation can output, the experiment on the common interface under the routed
handler of `ro` and `R₀` has, as transcript and state of `ro`, the measure of the experiment
against the adversary that holds `R`. -/
theorem map_run_simulateQ_handlerRouterImpl_unforgeableTranscriptExperiment_evalDistEq
    (ro : QueryImpl (unifSpec + hs) (StateT τ ProbComp))
    {R : PK → QueryImpl ext (StateT σ (OracleComp (unifSpec + hs)))}
    {R₀ : QueryImpl ext (StateT σ (OracleComp (unifSpec + hs)))}
    {sigAlg : SignatureAlg (OracleComp (unifSpec + hs)) M PK SK S}
    (hR : ∀ z ∈ support sigAlg.keygen, R z.1 = R₀)
    (adv : UnforgeableAdversary (sigAlg.map (simulateQ' (liftTypedImpl (ext := ext)))))
    (c : τ) (s : σ) :
    Prod.map id Prod.fst <$>
        (simulateQ (handlerRouterImpl ro R₀) (unforgeableTranscriptExperiment adv)).run (c, s) =ᵈ
      (simulateQ ro
        (unforgeableTranscriptExperiment (sigAlg := sigAlg) (adv.route R s))).run c := by
  rw [map_run_simulateQ_handlerRouterImpl_unforgeableTranscriptExperiment]
  exact run_simulateQ_unforgeableTranscriptExperiment_route_congr ro adv
    (fun z hz => (hR z hz).symm) s c

/-! ## The budget of the routed adversary -/

/-- An adversary over `unifSpec + ext`, read on the common interface, keeps its budget: its raw
queries are the hash queries of the common interface. -/
theorem UnforgeableAdversary.RomQueryBound.mapOracles_liftRawImpl
    {sigAlg' : SignatureAlg (OracleComp (unifSpec + ext)) M PK SK' S}
    {sigAlg : SignatureAlg (OracleComp (unifSpec + (hs + ext))) M PK SK S}
    {adv : UnforgeableAdversary sigAlg'} {qh qs : ℕ} (hadv : adv.RomQueryBound qh qs) :
    (adv.mapOracles liftRawImpl (sigAlg' := sigAlg)).RomQueryBound qh qs := by
  intro pk
  obtain ⟨hh, hsq⟩ := hadv pk
  rw [UnforgeableAdversary.mapOracles_main]
  refine ⟨hh.simulateQ_of_step ?_ ?_, hsq.simulateQ_of_step ?_ ?_⟩
  · rintro ((n | x) | m) ht <;> simp only [IsHashQuery] at ht
    exact (isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos
  · rintro ((n | x) | m) ht
    · exact (isQueryBoundP_query_iff _ _ _).2 fun h => h.elim
    · exact (ht trivial).elim
    · exact (isQueryBoundP_query_iff _ _ _).2 fun h => h.elim
  · rintro ((n | x) | m) ht <;> simp only [IsSignQuery] at ht
    exact (isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos
  · rintro ((n | x) | m) ht
    · exact (isQueryBoundP_query_iff _ _ _).2 fun h => h.elim
    · exact (isQueryBoundP_query_iff _ _ _).2 fun h => h.elim
    · exact (ht trivial).elim

/-- **The budget of the routed adversary.** If the router makes at most one hash query per raw
query, the adversary that holds it makes at most as many hash and signing queries as the
adversary on the common interface makes hash or raw queries and signing queries. -/
theorem UnforgeableAdversary.RomQueryBound.route
    {sigAlg' : SignatureAlg (OracleComp (unifSpec + (hs + ext))) M PK SK' S}
    {sigAlg : SignatureAlg (OracleComp (unifSpec + hs)) M PK SK S}
    {R : PK → QueryImpl ext (StateT σ (OracleComp (unifSpec + hs)))}
    (hR : ∀ pk x s, IsQueryBoundP ((R pk x).run s) (fun t => t.isRight) 1)
    {adv : UnforgeableAdversary sigAlg'} {qh qs : ℕ} (hadv : adv.RomQueryBound qh qs)
    (s₀ : σ) : (adv.route (sigAlg := sigAlg) R s₀).RomQueryBound qh qs := by
  intro pk
  obtain ⟨hh, hsq⟩ := hadv pk
  refine ⟨(isQueryBoundP_map_iff _ _ _).2 (hh.simulateQ_run_of_step ?_ ?_ s₀),
    (isQueryBoundP_map_iff _ _ _).2 (hsq.simulateQ_run_of_step ?_ ?_ s₀)⟩
  · rintro ((n | t | x) | m) ht s <;> simp only [IsHashQuery] at ht
    · simp [programRouterImpl, IsHashQuery]
    · refine isQueryBoundP_run_programRouterImpl_inr_inr x s ((hR pk x s).of_imp ?_)
      rintro (n | t) h <;> simp_all [IsHashQuery]
  · rintro ((n | t | x) | m) ht s
    · simp [programRouterImpl, IsHashQuery]
    · exact (ht trivial).elim
    · exact (ht trivial).elim
    · simp [programRouterImpl, IsHashQuery]
  · rintro ((n | t | x) | m) ht s <;> simp only [IsSignQuery] at ht
    simp [programRouterImpl, IsSignQuery]
  · rintro ((n | t | x) | m) ht s
    · simp [programRouterImpl, IsSignQuery]
    · simp [programRouterImpl, IsSignQuery]
    · refine isQueryBoundP_run_programRouterImpl_inr_inr x s ?_
      exact (isQueryBoundP_false _ 0).of_imp fun t h => by simp [IsSignQuery] at h
    · exact (ht trivial).elim

end SignatureAlg

namespace OracleComp.RandomOracleEncoding

variable {ι D M : Type} {spec : OracleSpec ι} [SampleableType M]
  [∀ t, SampleableType (spec.Range t)] (E : RandomOracleEncoding spec D M)

/-- The encoding passes the queries of a program over `unifSpec + (D →ₒ M)` on unchanged. -/
theorem encodeImpl_compose_liftRawImpl :
    E.encodeImpl ∘ₛ liftRawImpl (hs := spec) = QueryImpl.id' (unifSpec + (D →ₒ M)) := by
  funext u
  rcases u with n | x <;> simp [encodeImpl, liftRawImpl]

/-! ## The router of an encoding -/

section router

variable [DecidableEq D]

/-- The router of the typed world holding its table of private values as its own state: a raw
input `x` draws its private value from the table, as a lazy random oracle, and if `x` is read as a
typed point `q`, it queries `q` and completes the typed answer from the private value. -/
@[expose] noncomputable def tableRouter :
    QueryImpl (D →ₒ M) (StateT (D →ₒ M).QueryCache (OracleComp (unifSpec + spec))) :=
  fun x ↦ StateT.mk fun pv ↦ do
    let z ← (liftM (((D →ₒ M).randomOracle x).run pv) :
      OracleComp (unifSpec + spec) (M × (D →ₒ M).QueryCache))
    match E.route x with
    | some q => (fun r ↦ (E.complete q r z.1, z.2)) <$>
        (query (spec := unifSpec + spec) (.inr q) : OracleComp (unifSpec + spec) (spec.Range q))
    | none => pure z

variable {E}

/-- The router holding its table makes at most one query to the typed oracles. -/
theorem isQueryBoundP_run_tableRouter (x : D) (pv : (D →ₒ M).QueryCache) :
    IsQueryBoundP ((E.tableRouter x).run pv) (fun t => t.isRight) 1 := by
  simp only [tableRouter, StateT.run_mk]
  refine (isQueryBoundP_bind (n := 0) (m := 1) (isQueryBoundP_liftM_isRight _)
    fun z _ => ?_).mono le_rfl
  cases E.route x with
  | some q => simp
  | none => trivial

/-- At a raw input read as no typed point, the router holding its table makes no query to the
typed oracles. -/
theorem isQueryBoundP_run_tableRouter_of_route_eq_none {x : D} (hx : E.route x = none)
    (pv : (D →ₒ M).QueryCache) :
    IsQueryBoundP ((E.tableRouter x).run pv) (fun t => t.isRight) 0 := by
  simp only [tableRouter, StateT.run_mk, hx]
  exact isQueryBoundP_bind_zero _ _ (isQueryBoundP_liftM_isRight _) fun _ => trivial

variable [DecidableEq ι]

/-- The typed world is the handler-held router of the random oracle model of `spec` and the router
holding its table. -/
theorem typedImpl_eq_handlerRouterImpl :
    E.typedImpl = handlerRouterImpl spec.romImpl E.tableRouter := by
  funext u
  refine StateT.ext fun ⟨c, pv⟩ => ?_
  rcases u with n | t | x
  · exact typedImpl_inl_run n c pv
  · exact typedImpl_inr_inl_run t c pv
  · change (E.typedHashImpl (.inr x)).run (c, pv) = _
    rw [typedHashImpl_inr_run]
    simp only [handlerRouterImpl, tableRouter, StateT.run_mk, simulateQ_bind, StateT.run_bind,
      OracleSpec.simulateQ_romImpl_liftM_run, bind_map_left, map_bind]
    refine bind_congr fun z => ?_
    cases E.route x with
    | some q => simp [OracleSpec.romImpl]
    | none => simp

end router

/-! ## The routed adversary of an encoding -/

section experiment

open SignatureAlg

variable [DecidableEq D] {Msg PK SK SK' S : Type}

/-- The adversary holding the routers of encodings read off the public key keeps the budget of
the adversary over the single oracle. -/
theorem romQueryBound_route_tableRouter
    {sigAlg' : SignatureAlg (OracleComp (unifSpec + (D →ₒ M))) Msg PK SK' S}
    {sigAlg : SignatureAlg (OracleComp (unifSpec + spec)) Msg PK SK S}
    {Ek : PK → RandomOracleEncoding spec D M} {adv : UnforgeableAdversary sigAlg'} {qh qs : ℕ}
    (hadv : adv.RomQueryBound qh qs) (pv : (D →ₒ M).QueryCache) :
    ((adv.mapOracles liftRawImpl (sigAlg' := sigAlg.map (simulateQ' liftTypedImpl))).route
      (sigAlg := sigAlg) (fun pk => (Ek pk).tableRouter) pv).RomQueryBound qh qs :=
  hadv.mapOracles_liftRawImpl.route (fun _ x s => isQueryBoundP_run_tableRouter x s) pv

variable [DecidableEq ι]

/-- **The typed world is the random oracle model against the routed adversary.** The experiment
of a scheme over `unifSpec + spec`, lifted to the common interface, against an adversary on the
common interface, run in the typed world from `(c, pv)`, has as transcript and typed cache the run
in the random oracle model of `spec` from `c` of the experiment against the adversary that holds
the router and its table from `pv`. -/
theorem map_run_simulateQ_typedImpl_unforgeableTranscriptExperiment
    {sigAlg : SignatureAlg (OracleComp (unifSpec + spec)) Msg PK SK S}
    (adv : UnforgeableAdversary (sigAlg.map (simulateQ' (liftTypedImpl (ext := D →ₒ M)))))
    (c : spec.QueryCache) (pv : (D →ₒ M).QueryCache) :
    Prod.map id Prod.fst <$>
        (simulateQ E.typedImpl (unforgeableTranscriptExperiment adv)).run (c, pv) =
      (simulateQ spec.romImpl (unforgeableTranscriptExperiment (sigAlg := sigAlg)
        (adv.route (fun _ => E.tableRouter) pv))).run c := by
  rw [typedImpl_eq_handlerRouterImpl,
    map_run_simulateQ_handlerRouterImpl_unforgeableTranscriptExperiment]

/-- **The single-oracle world until a clash, against a routed adversary.** Let `Ek pk` be an
encoding read off the public key `pk`, equal to `E` at every public key the key generation can
output. An event of the transcript of the experiment of a scheme over `unifSpec + spec`, lifted
to the common interface, against an adversary on the common interface, run in the single-oracle
world of `E` from the empty cache, has probability at most that of the same event or a clash of
the final cache in the experiment of the scheme against the adversary that holds the router of
`Ek pk` and its table from the empty table, in the random oracle model of `spec` from the empty
cache. -/
theorem prEvent_simulateQ_singleImpl_run_unforgeableTranscriptExperiment_le
    {sigAlg : SignatureAlg (OracleComp (unifSpec + spec)) Msg PK SK S}
    (adv : UnforgeableAdversary (sigAlg.map (simulateQ' (liftTypedImpl (ext := D →ₒ M)))))
    {Ek : PK → RandomOracleEncoding spec D M} (hE : ∀ z ∈ support sigAlg.keygen, Ek z.1 = E)
    (P : UnforgeableTranscript Msg PK SK S → Prop) :
    Pr{let z ← (simulateQ E.singleImpl (unforgeableTranscriptExperiment adv)).run ∅}[P z.1] ≤
      Pr{let z ← (simulateQ spec.romImpl (unforgeableTranscriptExperiment (sigAlg := sigAlg)
        (adv.route (fun pk => (Ek pk).tableRouter) ∅))).run ∅}[P z.1 ∨ E.Clash z.2] := by
  refine (E.prEvent_simulateQ_singleImpl_run_le _ P).trans_eq ?_
  rw [typedImpl_eq_handlerRouterImpl]
  have h := map_run_simulateQ_handlerRouterImpl_unforgeableTranscriptExperiment_evalDistEq
    spec.romImpl (R := fun pk => (Ek pk).tableRouter) (R₀ := E.tableRouter)
    (fun z hz => by rw [hE z hz]) adv ∅ ∅
  rw [← h.prEvent_eq, prEvent_map]
  rfl

/-- **An adversary over the single oracle, routed.** Let `Ek pk` be an encoding read off the
public key `pk`, equal to `E` at every public key the key generation can output. An event of the
transcript of the experiment of a scheme over `unifSpec + spec`, with each typed query encoded by
`E`, against an adversary over `unifSpec + (D →ₒ M)`, in the random oracle model of the single
oracle from the empty cache, has probability at most that of the same event or a clash of the
final cache in the experiment of the scheme against the adversary that holds the router of
`Ek pk` and its table from the empty table, in the random oracle model of `spec` from the empty
cache. -/
theorem prEvent_simulateQ_romImpl_run_unforgeableTranscriptExperiment_le
    {sigAlg : SignatureAlg (OracleComp (unifSpec + spec)) Msg PK SK S}
    (adv : UnforgeableAdversary (sigAlg.map (simulateQ' (E.encodeImpl ∘ₛ liftTypedImpl))))
    {Ek : PK → RandomOracleEncoding spec D M} (hE : ∀ z ∈ support sigAlg.keygen, Ek z.1 = E)
    (P : UnforgeableTranscript Msg PK SK S → Prop) :
    Pr{let z ← (simulateQ (D →ₒ M).romImpl (unforgeableTranscriptExperiment adv)).run ∅}[
        P z.1] ≤
      Pr{let z ← (simulateQ spec.romImpl (unforgeableTranscriptExperiment (sigAlg := sigAlg)
        ((adv.mapOracles liftRawImpl (sigAlg' := sigAlg.map (simulateQ' liftTypedImpl))).route
          (fun pk => (Ek pk).tableRouter) ∅))).run ∅}[P z.1 ∨ E.Clash z.2] := by
  have hnat := simulateQ_unforgeableTranscriptExperiment E.encodeImpl
    (sigAlg := sigAlg.map (simulateQ' liftTypedImpl)) (adv.mapOracles liftRawImpl)
  rw [map_simulateQ'_map_simulateQ', UnforgeableAdversary.mapOracles_mapOracles,
    encodeImpl_compose_liftRawImpl, UnforgeableAdversary.mapOracles_id'] at hnat
  rw [← hnat, simulateQ_romImpl_simulateQ_encodeImpl]
  exact E.prEvent_simulateQ_singleImpl_run_unforgeableTranscriptExperiment_le _ hE P

end experiment

end OracleComp.RandomOracleEncoding
