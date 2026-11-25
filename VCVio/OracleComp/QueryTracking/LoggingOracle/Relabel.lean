/-
Copyright (c) 2026 Minhyuk Hwang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Minhyuk Hwang
-/

module

public import VCVio.OracleComp.QueryTracking.LoggingOracle.Core
public import VCVio.OracleComp.MapLens
public import VCVio.OracleComp.QueryTracking.RandomOracle.RoutingLens

/-!
# Relabelling logged queries

A program over `spec + (M →ₒ T)` can be run against a logging handler for `D →ₒ T` by first
transporting it (`OracleComp.mapLens`) along the lens `OracleComp.translateLens spec f`, which
sends each query `msg` to the query `f msg` and leaves `spec` alone. The resulting log records the
translated inputs `f msg`; running the program directly against the logging handler for the
composite `msg ↦ tagFn (f msg)` records the original inputs instead. The two runs agree up to
relabelling every log entry by `f` (`QueryImpl.run_simulateQ_withLogging_mapLens_translateLens`).

This is the simulation step of domain-extension reductions such as hash-and-MAC and hash-and-sign,
where the reduction hashes each chosen-message query before forwarding it. The other step is
collision extraction: `QueryLog.collisionCandidate f msg log` pairs `msg` with the first logged
message of the same image under `f`. When it is not a collision (`QueryLog.hasCollision`), an entry
of the relabelled log at `f msg` comes from an entry of the log at `msg`
(`QueryLog.mem_of_mem_relabel`, `QueryLog.mem_map_fst_of_mem_map_fst_relabel`).
-/

public section

universe u v

open OracleSpec OracleComp

namespace OracleSpec.QueryLog

variable {M : Type*} {D : Type*} {T : Type*}

/-- Relabel every entry of a `(M →ₒ T)` query log by `f`, keeping the responses. -/
@[expose] def relabel (f : M → D) (log : QueryLog (M →ₒ T)) : QueryLog (D →ₒ T) :=
  log.map fun e => ⟨f e.1, e.2⟩

@[simp]
lemma relabel_nil (f : M → D) : relabel f ([] : QueryLog (M →ₒ T)) = [] := rfl

@[simp]
lemma relabel_append (f : M → D) (log log' : QueryLog (M →ₒ T)) :
    relabel f (log ++ log') = relabel f log ++ relabel f log' :=
  List.map_append

@[simp]
lemma relabel_singleton (f : M → D) (msg : M) (τ : T) :
    relabel f ([⟨msg, τ⟩] : QueryLog (M →ₒ T)) = [⟨f msg, τ⟩] := rfl

/-- An entry of a relabelled log comes from an entry of the original log. -/
lemma mem_relabel_iff (f : M → D) (log : QueryLog (M →ₒ T)) (d : D) (τ : T) :
    (⟨d, τ⟩ : (_ : D) × T) ∈ relabel f log ↔ ∃ msg, f msg = d ∧ (⟨msg, τ⟩ : (_ : M) × T) ∈ log := by
  simp only [relabel, List.mem_map]
  constructor
  · rintro ⟨⟨msg, τ'⟩, hmem, heq⟩
    simp only [Sigma.mk.injEq, heq_eq_eq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    exact ⟨msg, rfl, hmem⟩
  · rintro ⟨msg, rfl, hmem⟩
    exact ⟨⟨msg, τ⟩, hmem, rfl⟩

/-- The forged message `msg` paired with the first logged message that differs from it and has the
same image under `f`, or `msg` twice if there is none. -/
@[expose] def collisionCandidate [DecidableEq M] [DecidableEq D] (f : M → D) (msg : M)
    (log : QueryLog (M →ₒ T)) : M × M :=
  match log.find? (fun e => decide (e.1 ≠ msg ∧ f e.1 = f msg)) with
  | some e => (msg, e.1)
  | none => (msg, msg)

/-- Whether `collisionCandidate f msg log` is a collision of `f`. -/
@[expose] def hasCollision [DecidableEq M] [DecidableEq D] (f : M → D) (msg : M)
    (log : QueryLog (M →ₒ T)) : Bool :=
  decide ((collisionCandidate f msg log).1 ≠ (collisionCandidate f msg log).2 ∧
    f (collisionCandidate f msg log).1 = f (collisionCandidate f msg log).2)

/-- A logged message that differs from `msg` and has the same image under `f` makes
`collisionCandidate f msg log` a collision. -/
theorem hasCollision_of_mem [DecidableEq M] [DecidableEq D] (f : M → D) (msg : M)
    (log : QueryLog (M →ₒ T)) {e : (_ : M) × T} (he : e ∈ log) (hne : e.1 ≠ msg)
    (hf : f e.1 = f msg) : hasCollision f msg log = true := by
  rw [hasCollision, decide_eq_true_eq]
  unfold collisionCandidate
  cases hfind : log.find? (fun e => decide (e.1 ≠ msg ∧ f e.1 = f msg)) with
  | none =>
    rw [List.find?_eq_none] at hfind
    exact absurd (decide_eq_true ⟨hne, hf⟩) (hfind e he)
  | some e' =>
    have hp := List.find?_some hfind
    simp only [decide_eq_true_eq] at hp
    exact ⟨fun h => hp.1 h.symm, hp.2.symm⟩

/-- Without a collision, a pair whose image under `f` occurs in the relabelled log occurs in the
log itself. -/
theorem mem_of_mem_relabel [DecidableEq M] [DecidableEq D] (f : M → D) (msg : M) (τ : T)
    (log : QueryLog (M →ₒ T)) (hcoll : hasCollision f msg log = false)
    (hmem : (⟨f msg, τ⟩ : (_ : D) × T) ∈ relabel f log) : (⟨msg, τ⟩ : (_ : M) × T) ∈ log := by
  obtain ⟨msg', hf, hmem'⟩ := (mem_relabel_iff f log _ τ).1 hmem
  by_cases hne : msg' = msg
  · exact hne ▸ hmem'
  · simp [hasCollision_of_mem f msg log hmem' hne hf] at hcoll

/-- Without a collision, a message whose image under `f` was queried in the relabelled log was
queried in the log itself. -/
theorem mem_map_fst_of_mem_map_fst_relabel [DecidableEq M] [DecidableEq D] (f : M → D) (msg : M)
    (log : QueryLog (M →ₒ T)) (hcoll : hasCollision f msg log = false)
    (hmem : f msg ∈ (relabel f log).map (·.1)) : msg ∈ log.map (·.1) := by
  simp only [relabel, List.map_map, List.mem_map, Function.comp_apply] at hmem ⊢
  obtain ⟨e, he, hf⟩ := hmem
  by_cases hne : e.1 = msg
  · exact ⟨e, he, hne⟩
  · simp [hasCollision_of_mem f msg log he hne hf] at hcoll

end OracleSpec.QueryLog

namespace QueryImpl

variable {ι : Type*} {spec : OracleSpec.{_, u} ι} {α A B : Type u} {m : Type u → Type v}
  [Monad m] [LawfulMonad m]

/-- Two logging handlers whose logs agree up to mapping each entry by `e` give runs whose logs
agree up to the same map. -/
theorem run_simulateQ_map_log (e : A → B) (impl₁ : QueryImpl spec (WriterT (List A) m))
    (impl₂ : QueryImpl spec (WriterT (List B) m))
    (h : ∀ t, (impl₂ t).run = Prod.map id (List.map e) <$> (impl₁ t).run)
    (oa : OracleComp spec α) :
    (simulateQ impl₂ oa).run = Prod.map id (List.map e) <$> (simulateQ impl₁ oa).run := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t k ih =>
    simp [h, ih, map_bind, bind_map_left]

/-- Running a computation of the ambient oracles `spec`, lifted into `spec + spec'`, against
`spec.passthrough + impl` runs it unchanged with an empty log. -/
theorem run_simulateQ_passthrough_add_liftM {κ : Type*} {spec' : OracleSpec.{_, u} κ}
    (impl : QueryImpl spec' (WriterT (List A) (OracleComp spec))) (oa : OracleComp spec α) :
    (simulateQ (spec.passthrough + impl) (liftM oa : OracleComp (spec + spec') α)).run =
      (fun x => (x, [])) <$> oa := by
  rw [passthrough_add, simulateQ_add_liftM_left]
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t f ih => simp [ih, map_bind]

end QueryImpl

namespace OracleComp

variable {ι : Type*} {M D T : Type u}

/-- The lens that sends each `(M →ₒ T)` query `msg` to the `(D →ₒ T)` query `f msg` and leaves the
queries of `spec` unchanged: the identity lens on `spec` beside `RandomOracleRouting.lens f`. -/
@[expose] def translateLens (spec : OracleSpec.{_, u} ι) (f : M → D) :
    PFunctor.Lens (spec + (M →ₒ T)).toPFunctor (spec + (D →ₒ T)).toPFunctor :=
  PFunctor.Lens.sumMap (PFunctor.Lens.id spec.toPFunctor) (RandomOracleRouting.lens f)

end OracleComp

namespace QueryImpl

variable {ι : Type*} {spec : OracleSpec.{_, u} ι} {α : Type u} {M D T : Type u}

/-- Running a program transported along `translateLens spec f`, which sends each `(M →ₒ T)` query
`msg` to the query `f msg`, against a logging handler for `tagFn` is the run against the logging
handler for any `tagFn'` that answers `msg` as `tagFn` answers `f msg`, with its log relabelled by
`f`. -/
theorem run_simulateQ_withLogging_mapLens_translateLens
    (tagFn : QueryImpl (D →ₒ T) (OracleComp spec)) (tagFn' : QueryImpl (M →ₒ T) (OracleComp spec))
    (f : M → D)
    (htag : ∀ msg, tagFn' msg = tagFn (f msg)) (oa : OracleComp (spec + (M →ₒ T)) α) :
    (simulateQ (spec.passthrough + tagFn.withLogging)
        (oa.mapLens (translateLens spec f))).run =
      Prod.map id (QueryLog.relabel f) <$>
        (simulateQ (spec.passthrough + tagFn'.withLogging) oa).run := by
  rw [OracleComp.simulateQ_mapLens]
  refine run_simulateQ_map_log _ _ _ (fun t => ?_) oa
  rcases t with n | msg
  · simp [QueryImpl.comapLens_apply, translateLens, PFunctor.Lens.sumMap]
  · simp [QueryImpl.comapLens_apply, translateLens, PFunctor.Lens.sumMap, RandomOracleRouting.lens,
    htag]

end QueryImpl
