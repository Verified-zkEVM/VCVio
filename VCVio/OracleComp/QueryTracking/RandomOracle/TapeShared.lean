/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation
public import VCVio.OracleComp.QueryTracking.RandomOracle.Tape

/-!
# The answer tape of a shared lazy random oracle

`tapeCachingImplAdd` is the shared-interface form of `AnswerTape.tapeCachingImpl`: over
`unifSpec + (D →ₒ R)` it forwards a private `unifSpec` query to the ambient sampler, touching
neither the answer cache nor the tape, and answers a hash query off the tape. Averaged over a
list of `m` independent uniform values it *is* `unifFwdImpl (D →ₒ R) + randomOracle`, jointly in
the output and the final cache (`evalDist_run_unifFwdImpl_add_randomOracle_eq_tapeList`). That
is the shape an adversary run takes — private sampling forwarded, hash queries lazily cached —
so it is the form in which the tape identification of `Tape.lean` applies to a real run.

A private-sampling step is the same sample on both sides and leaves the whole state alone, so
identifying it amounts to exchanging it with the tape draw that precedes the run
(`evalDist_bind_bind_swap_of_countable`). Its shape hands the sampler back existentially
(`exists_run_inl`) instead of naming it, because the `liftM (OracleSpec.query i)` that realises
the step does not unify across a lemma boundary.

The position bookkeeping lifts along the same split. `positionAuxAdd` records nothing for a
private query and defers to `AnswerTape.positionAux` for a hash query, so a run maintains the
same `AnswerTape.PositionInv`, and
`exists_pos_of_mem_support_run_tapeCachingImplAdd` is the consequence a product bound over the
tape consumes: every entry of the final cache is the tape value at its own position, and
distinct entries sit at distinct positions.
`evalDist_run_unifFwdImpl_add_randomOracle_setOf_le_of_transport` is the packaged consumer,
turning a tape event of small mass into a bound on the shared run.

## Scope

* The hash interface is the single-index `D →ₒ R`, as in `Tape.lean`: one tape of values of a
  single type `R` is consumed in order, so a genuinely indexed hash interface with varying
  range types is not covered.
* Nothing here bounds the mass of any tape event. The tape event and its bound are the
  caller's, supplied to the transport theorem as `E` and `hE`.
* No query bound relates the tape length `m` to the number of queries `oa` makes: the
  identification holds for every `m`, with the tape-consuming oracle sampling freshly once the
  tape runs out. The position invariant's conclusion does need the run's final cache to be
  small enough that the fallback answers cannot have been reached.
-/

public section

open OracleComp OracleSpec MeasureTheory
open scoped ENNReal

namespace AnswerTape

variable {D R : Type} [DecidableEq D] [SampleableType R]

/-! ## The tape-consuming shared oracle -/

/-- The tape-consuming lazy oracle for the shared interface `unifSpec + (D →ₒ R)`: a private
`unifSpec` query is forwarded to the ambient sampler and touches neither the cache nor the
tape, while a hash query is answered by `tapeCachingImpl`. -/
def tapeCachingImplAdd (D R : Type) [DecidableEq D] [SampleableType R] :
    QueryImpl (unifSpec + (D →ₒ R)) (StateT ((D →ₒ R).QueryCache × List R) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT ((D →ₒ R).QueryCache × List R) ProbComp) +
    tapeCachingImpl D R

theorem tapeCachingImplAdd_apply_inr (t : D) :
    tapeCachingImplAdd D R (Sum.inr t) = tapeCachingImpl D R t := by
  unfold tapeCachingImplAdd
  rfl

/-- **A private-sampling step is the same sample on both sides.** It leaves the cache untouched
under `unifFwdImpl (D →ₒ R) + randomOracle`, and leaves the cache and the tape untouched under
`tapeCachingImplAdd`. The sampler is handed back existentially rather than named. -/
theorem exists_run_inl (i : unifSpec.Domain) (c : (D →ₒ R).QueryCache) :
    ∃ samp : ProbComp (unifSpec.Range i),
      ((unifFwdImpl (D →ₒ R) + (D →ₒ R).randomOracle) (Sum.inl i)).run c =
          (fun u => (u, c)) <$> samp ∧
        ∀ l : List R, (tapeCachingImplAdd D R (Sum.inl i)).run (c, l) =
          (fun u => (u, (c, l))) <$> samp :=
  ⟨liftM (OracleSpec.query i), by simp [unifFwdImpl],
    fun l => by simp [tapeCachingImplAdd]⟩

/-! ## The identification -/

/-- **The shared lazy random oracle is the tape-consuming shared oracle averaged over an iid
tape.** For every tape length `m`, running `oa` under `unifFwdImpl (D →ₒ R) + randomOracle` from
cache `c` has the same joint distribution of output and final cache as drawing `m` independent
uniform answers, running `oa` under `tapeCachingImplAdd` from `c` with that tape, and forgetting
the unconsumed tape. -/
theorem evalDist_run_unifFwdImpl_add_randomOracle_eq_tapeList {α : Type}
    (oa : OracleComp (unifSpec + (D →ₒ R)) α) (c : (D →ₒ R).QueryCache) (m : ℕ) :
    letI : MeasurableSpace (α × (D →ₒ R).QueryCache) := ⊤
    𝒟[(simulateQ (unifFwdImpl (D →ₒ R) + (D →ₒ R).randomOracle) oa).run c] =
      𝒟[(do let l ← tapeList R m
            let z ← (simulateQ (tapeCachingImplAdd D R) oa).run (c, l)
            return (z.1, z.2.1))] := by
  let _ : MeasurableSpace (α × (D →ₒ R).QueryCache) := ⊤
  let _ : MeasurableSpace R := ⊤
  let _ : MeasurableSpace (List R) := ⊤
  induction oa using OracleComp.inductionOn generalizing c m with
  | pure x =>
    simp only [simulateQ_pure, StateT.run_pure, pure_bind]
    rw [_root_.evalDist_bind_const]
    have hprob : IsProbabilityMeasure 𝒟[tapeList R m] := by
      rw [tapeList, evalDist_map_of_discrete]
      infer_instance
    rw [measure_univ, one_smul]
  | query_bind t k ih =>
    have hredL : (simulateQ (unifFwdImpl (D →ₒ R) + (D →ₒ R).randomOracle)
          (liftM ((unifSpec + (D →ₒ R)).query t) >>= k)).run c =
        (((unifFwdImpl (D →ₒ R) + (D →ₒ R).randomOracle) t).run c) >>= fun p =>
          (simulateQ (unifFwdImpl (D →ₒ R) + (D →ₒ R).randomOracle) (k p.1)).run p.2 := by
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    have hredR : ∀ l : List R,
        (simulateQ (tapeCachingImplAdd D R)
            (liftM ((unifSpec + (D →ₒ R)).query t) >>= k)).run (c, l) =
          ((tapeCachingImplAdd D R t).run (c, l)) >>= fun p =>
            (simulateQ (tapeCachingImplAdd D R) (k p.1)).run p.2 := fun l => by
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rw [hredL]
    simp only [hredR]
    rcases t with i | t
    · obtain ⟨samp, hL, hR⟩ := exists_run_inl (D := D) (R := R) i c
      rw [hL]
      simp only [hR, map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind]
      rw [evalDist_bind_bind_swap_of_countable (tapeList R m) samp]
      rw [evalDist_bind_of_discrete, evalDist_bind_of_discrete]
      apply Measure.bind_congr_right
      filter_upwards [] with u
      exact ih u c m
    · rw [QueryImpl.add_apply_inr, randomOracle.run_eq]
      simp only [tapeCachingImplAdd_apply_inr]
      rcases hc : c t with _ | u
      · cases m with
        | zero =>
          simp only [tapeList_zero, pure_bind, tapeCachingImpl_run_nil hc,
            map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
          rw [evalDist_bind_of_discrete, evalDist_bind_of_discrete]
          apply Measure.bind_congr_right
          filter_upwards [] with u
          simpa only [tapeList_zero, pure_bind] using ih u (c.cacheQuery t u) 0
        | succ m' =>
          simp only [tapeList_succ, bind_assoc, pure_bind, tapeCachingImpl_run_cons hc]
          rw [evalDist_bind_of_discrete, evalDist_bind_of_discrete]
          apply Measure.bind_congr_right
          filter_upwards [] with u
          exact ih u (c.cacheQuery t u) m'
      · simp only [tapeCachingImpl_run_some hc, pure_bind]
        exact ih u c m

/-! ## The position instrumentation -/

/-- The position bookkeeping of one `tapeCachingImplAdd` step: a private `unifSpec` query
records nothing, and a hash query records what `positionAux` records. -/
def positionAuxAdd (D R : Type) [DecidableEq D] :
    (t : (unifSpec + (D →ₒ R)).Domain) → ((D →ₒ R).QueryCache × List R) →
      (unifSpec + (D →ₒ R)).Range t → ((D →ₒ R).QueryCache × List R) →
      ((D → Option ℕ) × ℕ) → (D → Option ℕ) × ℕ
  | Sum.inl _ => fun _ _ _ p => p
  | Sum.inr t => positionAux D R t

omit [SampleableType R] in
private theorem positionAuxAdd_inl (i : unifSpec.Domain)
    (s : (D →ₒ R).QueryCache × List R) (x : unifSpec.Range i)
    (s' : (D →ₒ R).QueryCache × List R) (p : (D → Option ℕ) × ℕ) :
    positionAuxAdd D R (Sum.inl i) s x s' p = p := by
  unfold positionAuxAdd
  rfl

private theorem extendState_tapeCachingImplAdd_inr (t : D) :
    QueryImpl.extendState (tapeCachingImplAdd D R) (positionAuxAdd D R) (Sum.inr t) =
      QueryImpl.extendState (tapeCachingImpl D R) (positionAux D R) t := by
  unfold QueryImpl.extendState positionAuxAdd
  simp only [tapeCachingImplAdd_apply_inr]
  rfl

/-- Every step of the instrumented tape-consuming shared oracle preserves `PositionInv`. -/
theorem positionInvAdd_step (L : List R) (t : (unifSpec + (D →ₒ R)).Domain)
    (s : ((D →ₒ R).QueryCache × List R) × (D → Option ℕ) × ℕ)
    (hs : PositionInv L s.1.1 s.1.2 s.2.1 s.2.2)
    (y : (unifSpec + (D →ₒ R)).Range t × ((D →ₒ R).QueryCache × List R) × (D → Option ℕ) × ℕ)
    (hy : y ∈ support
      ((QueryImpl.extendState (tapeCachingImplAdd D R) (positionAuxAdd D R) t).run s)) :
    PositionInv L y.2.1.1 y.2.1.2 y.2.2.1 y.2.2.2 := by
  rcases t with i | t
  · obtain ⟨⟨c, l⟩, pm, nx⟩ := s
    obtain ⟨samp, -, hR⟩ := exists_run_inl (D := D) (R := R) i c
    rw [QueryImpl.extendState_apply, hR l, mem_support_bind_iff] at hy
    obtain ⟨p, hp, hy⟩ := hy
    rw [support_map] at hp
    obtain ⟨u, -, rfl⟩ := hp
    rw [support_pure, Set.mem_singleton_iff] at hy
    subst hy
    simpa only [positionAuxAdd_inl] using hs
  · refine positionInv_step L t s hs y ?_
    rwa [← extendState_tapeCachingImplAdd_inr t]

/-- **Every cache entry of a tape-consuming shared run sits at its own tape position.** In a run
of `oa` under `tapeCachingImplAdd` from the empty cache on the length-`q` tape `v`, if the final
cache has at most `q` entries then each of its entries is the tape value at a position of the
tape, and distinct cached queries have distinct positions. -/
theorem exists_pos_of_mem_support_run_tapeCachingImplAdd {α : Type} {q : ℕ} (v : Fin q → R)
    (oa : OracleComp (unifSpec + (D →ₒ R)) α) {z : α × (D →ₒ R).QueryCache × List R}
    (hz : z ∈ support ((simulateQ (tapeCachingImplAdd D R) oa).run (∅, List.ofFn v)))
    (hq : z.2.1.enncard ≤ (q : ℝ≥0∞)) :
    ∃ pos : D → Option (Fin q),
      (∀ t u, z.2.1 t = some u → ∃ i, pos t = some i ∧ u = v i) ∧
      (∀ t t' i, pos t = some i → pos t' = some i → t = t') := by
  rw [← extendState_run_proj_eq (tapeCachingImplAdd D R) (positionAuxAdd D R) oa
    (∅, List.ofFn v) ((fun _ => none), 0), support_map] at hz
  obtain ⟨y, hy, hyz⟩ := hz
  have hinv := simulateQ_run_preserves_inv_of_query
    (QueryImpl.extendState (tapeCachingImplAdd D R) (positionAuxAdd D R))
    (fun s => PositionInv (List.ofFn v) s.1.1 s.1.2 s.2.1 s.2.2)
    (fun t s hs => positionInvAdd_step (List.ofFn v) t s hs) oa _
    (PositionInv.empty (List.ofFn v)) y hy
  have hc : y.2.1.1 = z.2.1 := by rw [← hyz]; rfl
  exact PositionInv.exists_pos (hc ▸ hinv) hq

/-! ## Transporting a tape bound -/

variable [MeasurableSpace R] [DiscreteMeasurableSpace R]

/-- **Transporting a tape bound to a shared lazy random-oracle run.** If the tape event `E` has
mass at most `b`, and off `E` no run of `oa` under `tapeCachingImplAdd` on that tape can leave a
final cache satisfying `P`, then the shared lazy random-oracle run leaves a cache satisfying `P`
with mass at most `b`. -/
theorem evalDist_run_unifFwdImpl_add_randomOracle_setOf_le_of_transport {α : Type} (q : ℕ)
    (oa : OracleComp (unifSpec + (D →ₒ R)) α) (P : (D →ₒ R).QueryCache → Prop)
    (E : Set (Fin q → R)) (b : ℝ≥0∞) (hE : 𝒟[answerTape R q] E ≤ b)
    (htransport : ∀ v : Fin q → R, v ∉ E →
      ∀ z ∈ support ((simulateQ (tapeCachingImplAdd D R) oa).run (∅, List.ofFn v)), ¬ P z.2.1) :
    letI : MeasurableSpace (α × (D →ₒ R).QueryCache) := ⊤
    𝒟[(simulateQ (unifFwdImpl (D →ₒ R) + (D →ₒ R).randomOracle) oa).run ∅] {z | P z.2} ≤ b := by
  classical
  let _ : MeasurableSpace (α × (D →ₒ R).QueryCache) := ⊤
  rw [evalDist_run_unifFwdImpl_add_randomOracle_eq_tapeList oa ∅ q]
  refine le_trans ?_ hE
  simp only [tapeList, map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
  refine evalDist_bind_apply_le_of_forall_notMem_eq_zero _ _ MeasurableSet.of_discrete
    MeasurableSet.of_discrete fun v hv => ?_
  refine evalDist.apply_eq_zero_of_disjoint_support _ MeasurableSet.of_discrete fun z hz => ?_
  rw [mem_support_bind_iff] at hz
  obtain ⟨w, hw, hz⟩ := hz
  rw [support_pure, Set.mem_singleton_iff] at hz
  subst hz
  exact htransport v hv w hw

end AnswerTape
