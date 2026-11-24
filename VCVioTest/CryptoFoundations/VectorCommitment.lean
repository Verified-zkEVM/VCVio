/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import VCVio.CryptoFoundations.VectorCommitment.Hiding
public import VCVio.CryptoFoundations.VectorCommitment.PositionBinding
public import VCVio.CryptoFoundations.VectorCommitment.RomCompleteness
public import VCVio.CryptoFoundations.MerkleTree.Salted.Defs

/-!
# Vector commitment security checks

A scheme that commits to nothing is hiding against every adversary. A scheme that commits to the
message in the clear is not: an adversary that reads the commitment has advantage one, so it is not
two-message hiding below error one even against adversaries that make no oracle queries and open no
positions, and it is simulation hiding only at error at least `1 / 2`. A check that accepts
everything is not position binding: two conflicting openings of one commitment win with probability
one. A check that compares the claimed values with a commitment in the clear is position binding
with advantage zero. The constant scheme satisfies `SimulationHiding` with error zero by a
simulator that makes no oracle queries, and hence `TwoMessageHiding` with error zero.

The one-time pad over the oracle is a scheme that uses the random oracle and is both binding and
hiding at small error: it commits to the message bit masked with the oracle's answer at `()`. It is
two-message hiding with error zero against adversaries that make no oracle queries, whatever the
opening size, and position binding with advantage zero against every adversary. An adversary that
makes one oracle query unmasks the commitment and has advantage one, so the query budget matters.

The salted Merkle commitment accepts honest openings with probability one under the lazily sampled
random oracle of the two advantages, and both advantages can be stated for it.
-/

public section

open OracleComp OracleSpec VectorCommitment

namespace VectorCommitmentTest

/-- Commits to the message itself; the opening is trivial and the check accepts exactly the
claimed values that agree with the commitment. -/
def transparent : VectorCommitment Unit Unit Bool (Fin 1 → Bool) Unit Unit 1 where
  commit m := pure (m, ())
  opening _ _ := pure ()
  check cm ans _ := pure (decide (PartialVec.Agrees (fun i ↦ some (cm i)) ans))

/-- Commits to nothing; the check accepts everything. -/
def constant : VectorCommitment Unit Unit Bool Unit Unit Unit 1 where
  commit _ := pure ((), ())
  opening _ _ := pure ()
  check _ _ _ := pure true

/-- Chooses two different messages, opens nothing, and reads the commitment. -/
def reader : TwoMessageHidingAdversary Unit Unit Bool (Fin 1 → Bool) Unit 1 where
  State := Unit
  choose := pure (fun _ ↦ false, fun _ ↦ true, ∅, ())
  distinguish _ cm _ := pure (cm 0)

/-! ## Hiding -/

/-- Both worlds of the constant scheme are the same computation. -/
example (adversary : TwoMessageHidingAdversary Unit Unit Bool Unit Unit 1) :
    constant.twoMessageHidingExperiment adversary true =
      constant.twoMessageHidingExperiment adversary false := rfl

/-- The constant scheme gives every adversary advantage zero. -/
example (adversary : TwoMessageHidingAdversary Unit Unit Bool Unit Unit 1) :
    constant.twoMessageHidingAdvantage adversary = 0 := by
  rw [twoMessageHidingAdvantage_eq, show constant.twoMessageHidingExperiment adversary true =
    constant.twoMessageHidingExperiment adversary false from rfl, ENNReal.absDiff_self]

/-- The reader's experiment returns the world bit. -/
theorem transparent_twoMessageHidingExperiment (b : Bool) :
    transparent.twoMessageHidingExperiment reader b = pure b := by
  have agree : PartialVec.restrict (fun _ : Fin 1 ↦ false) ∅ =
      PartialVec.restrict (fun _ ↦ true) ∅ := by
    funext i
    simp [PartialVec.restrict_apply]
  cases b <;> simp [twoMessageHidingExperiment, transparent, reader, agree]

/-- The transparent scheme gives the reader advantage one. -/
theorem transparent_twoMessageHidingAdvantage_reader :
    transparent.twoMessageHidingAdvantage reader = 1 := by
  simp [twoMessageHidingAdvantage_eq, transparent_twoMessageHidingExperiment,
    ProbCompRuntime.rom_evalDist]

/-- The reader makes no oracle queries. -/
theorem reader_makesAtMostQueries_zero : reader.MakesAtMostQueries 0 := by
  intro cm pf
  simp [reader]

/-- The reader opens no positions. -/
theorem reader_opensExactly_zero : reader.OpensExactly 0 := by
  intro c hc
  simp only [reader, support_pure] at hc
  subst hc
  rfl

/-- The transparent scheme is not two-message hiding below error one, even against adversaries
that make no oracle queries and open no positions. -/
theorem not_transparent_twoMessageHiding {ε : ENNReal} (hε : ε < 1) :
    ¬ transparent.TwoMessageHiding 0 0 ε := fun h ↦
  hε.not_ge (transparent_twoMessageHidingAdvantage_reader ▸
    h reader reader_makesAtMostQueries_zero reader_opensExactly_zero)

/-- The reader's world adversaries inherit its zero query budget. -/
example (b : Bool) : (reader.toSimulation b).MakesAtMostQueries 0 :=
  TwoMessageHidingAdversary.makesAtMostQueries_toSimulation reader_makesAtMostQueries_zero b

/-- The reader's world adversaries inherit its opening size. -/
example (b : Bool) : (reader.toSimulation b).OpensExactly 0 :=
  TwoMessageHidingAdversary.opensExactly_toSimulation reader_opensExactly_zero b

/-- A simulator for the constant scheme, which needs no information about the message. -/
def constantSimulator : HidingSimulator Unit Unit Bool Unit Unit 1 := fun _ _ ↦ pure ((), ())

/-- The constant scheme's real and simulated worlds are the same computation. -/
theorem constant_simulationHidingAdvantage
    (adversary : SimulationHidingAdversary Unit Unit Bool Unit Unit 1) :
    constant.simulationHidingAdvantage constantSimulator adversary = 0 := by
  have h : constant.simulationHidingRealExperiment adversary =
      simulationHidingIdealExperiment constantSimulator adversary := by
    simp [simulationHidingRealExperiment, simulationHidingIdealExperiment, constant,
      constantSimulator]
  rw [simulationHidingAdvantage_eq, h, ENNReal.absDiff_self]

/-- The constant simulator makes no oracle queries. -/
theorem constantSimulator_makesAtMostQueries_zero : constantSimulator.MakesAtMostQueries 0 := by
  intro Q ans
  simp [constantSimulator]

/-- The constant scheme is simulation hiding with error `0` at every opening size and query
budget, by one simulator that makes no oracle queries. -/
theorem constant_simulationHiding : constant.SimulationHiding 0 fun _ _ ↦ 0 :=
  ⟨constantSimulator, constantSimulator_makesAtMostQueries_zero,
    fun _ _ adversary _ _ ↦ (constant_simulationHidingAdvantage adversary).le⟩

/-- The constant scheme is two-message hiding with error `0`. -/
example (t q : ℕ) : constant.TwoMessageHiding t q 0 := by
  simpa using constant_simulationHiding.twoMessageHiding t q

/-- Chooses the message that is `c` everywhere, opens nothing, and checks whether the commitment
reads `c`. -/
def constantReader (c : Bool) : SimulationHidingAdversary Unit Unit Bool (Fin 1 → Bool) Unit 1 where
  State := Unit
  choose := pure (fun _ ↦ c, ∅, ())
  distinguish _ cm _ := pure (cm 0 == c)

/-- The constant readers make no oracle queries. -/
theorem constantReader_makesAtMostQueries_zero (c : Bool) :
    (constantReader c).MakesAtMostQueries 0 := by
  intro cm pf
  simp [constantReader]

/-- The constant readers open no positions. -/
theorem constantReader_opensExactly_zero (c : Bool) : (constantReader c).OpensExactly 0 := by
  intro x hx
  simp only [constantReader, support_pure] at hx
  subst hx
  rfl

/-- Against the transparent scheme, one is at most the simulation-hiding advantage of the constant
reader for `c` plus the probability that the simulator's commitment on an empty opening reads
`c`. -/
theorem one_le_transparent_simulationHidingAdvantage_add
    (simulator : HidingSimulator Unit Unit Bool (Fin 1 → Bool) Unit 1) (c : Bool) :
    1 ≤ transparent.simulationHidingAdvantage simulator (constantReader c) +
      (ProbCompRuntime.rom (Unit →ₒ Unit)).evalDist
        ((fun x ↦ x.1 0) <$> simulator ∅ (fun _ ↦ none)) {c} := by
  have hreal : transparent.simulationHidingRealExperiment (constantReader c) = pure true := by
    simp [simulationHidingRealExperiment, transparent, constantReader]
  have hideal : simulationHidingIdealExperiment simulator (constantReader c) =
      (fun b ↦ b == c) <$> ((fun x ↦ x.1 0) <$> simulator ∅ (fun _ ↦ none)) := by
    have hres : PartialVec.restrict (fun _ : Fin 1 ↦ c) ∅ = fun _ ↦ none := by
      funext i
      simp
    simp [simulationHidingIdealExperiment, constantReader, hres]
  rw [simulationHidingAdvantage_eq, hreal, hideal,
    ProbCompRuntime.evalDist_map _ _ (by fun_prop),
    MeasureTheory.Measure.map_apply (by fun_prop) (measurableSet_singleton true)]
  have hpre : (fun b : Bool ↦ b == c) ⁻¹' {true} = {c} := by
    ext b
    simp
  have hone : (ProbCompRuntime.rom (Unit →ₒ Unit)).evalDist (pure true) {true} = 1 := by
    simp [ProbCompRuntime.rom_evalDist]
  rw [hpre, hone, ENNReal.absDiff]
  exact le_tsub_add.trans (add_le_add le_self_add le_rfl)

/-- The transparent scheme is not simulation hiding below error `1 / 2`, even against adversaries
that make no oracle queries and open no positions: the simulator sees nothing of the message, so
its commitment reads one of the two constant messages with probability at most `1 / 2`. -/
theorem one_half_le_of_transparent_simulationHidingWith
    (simulator : HidingSimulator Unit Unit Bool (Fin 1 → Bool) Unit 1) {ε : ENNReal}
    (h : transparent.SimulationHidingWith simulator 0 0 ε) : 1 / 2 ≤ ε := by
  set μ := (ProbCompRuntime.rom (Unit →ₒ Unit)).evalDist
    ((fun x ↦ x.1 0) <$> simulator ∅ (fun _ ↦ none))
  have hle (c : Bool) : 1 ≤ ε + μ {c} :=
    (one_le_transparent_simulationHidingAdvantage_add simulator c).trans
      (add_le_add (h _ (constantReader_makesAtMostQueries_zero c)
        (constantReader_opensExactly_zero c)) le_rfl)
  have hsum : μ {false} + μ {true} ≤ 1 := by
    rw [← MeasureTheory.measure_union (Set.disjoint_singleton.mpr (by decide))
      (measurableSet_singleton true)]
    exact (MeasureTheory.measure_mono (Set.subset_univ _)).trans
      (ProbCompRuntime.evalDist_apply_univ_le_one _ _)
  have h2 : 1 + 1 ≤ ε * 2 + 1 := calc
    1 + 1 ≤ (ε + μ {false}) + (ε + μ {true}) := add_le_add (hle false) (hle true)
    _ = ε * 2 + (μ {false} + μ {true}) := by ring
    _ ≤ ε * 2 + 1 := add_le_add le_rfl hsum
  exact ENNReal.div_le_of_le_mul ((ENNReal.add_le_add_iff_right ENNReal.one_ne_top).mp h2)

/-! ## Position binding -/

/-- Opens position `0` of one commitment to both `false` and `true`. -/
def forger : PositionBindingAdversary Unit Unit Bool Unit Unit 1 :=
  pure ((), (fun _ ↦ some false, ()), (fun _ ↦ some true, ()))

/-- A check that accepts everything is broken with probability one. -/
example : constant.positionBindingAdvantage forger = 1 := by
  simp [positionBindingAdvantage_def, positionBindingExperiment, forger, constant,
    PartialVec.Conflict, ProbCompRuntime.rom_evalDist]

/-- The forger makes no oracle queries. -/
example : forger.MakesAtMostQueries 0 := by
  simp [PositionBindingAdversary.MakesAtMostQueries, forger]

/-- A check that compares the claimed values with the commitment is never broken: two conflicting
openings cannot both agree with one commitment. -/
example (adversary : PositionBindingAdversary Unit Unit Bool (Fin 1 → Bool) Unit 1) :
    transparent.positionBindingAdvantage adversary = 0 := by
  have h : transparent.positionBindingExperiment adversary = (fun _ ↦ false) <$> adversary := by
    rw [positionBindingExperiment, map_eq_bind_pure_comp]
    congr 1
    funext x
    obtain ⟨cm, ⟨a₁, pf₁⟩, a₂, pf₂⟩ := x
    dsimp only
    split_ifs with hc
    · obtain ⟨q, x, y, hx, hy, hxy⟩ := hc
      simp only [transparent, pure_bind, Function.comp_apply, pure_inj, Bool.and_eq_false_iff,
        decide_eq_false_iff_not]
      by_contra hagree
      simp only [not_or, not_not] at hagree
      exact hxy (Option.some_injective _ ((hagree.1 q x hx).symm.trans (hagree.2 q y hy)))
    · rfl
  rw [positionBindingAdvantage_def, h, ProbCompRuntime.evalDist_map _ _ measurable_const,
    MeasureTheory.Measure.map_apply measurable_const (measurableSet_singleton true)]
  simp

/-- Identical openings never conflict. -/
example (a : PartialVec 1 Bool) : ¬ PartialVec.Conflict a a := by simp

/-- Conflict is symmetric. -/
example (a b : PartialVec 1 Bool) : PartialVec.Conflict a b ↔ PartialVec.Conflict b a :=
  PartialVec.conflict_comm

/-! ## A one-time pad over the oracle

`pad` uses the random oracle: `Commit` masks the message bit with the oracle's answer at `()`, and
`Check` queries the oracle again to unmask. An adversary that makes no oracle query sees a one-time
pad; an adversary that queries `()` once unmasks the commitment. -/

section Pad

/-- A computation that makes no query to the oracle is a lifted `ProbComp`. -/
theorem exists_liftM_eq_of_isQueryBoundP_zero {p : ℕ ⊕ Unit → Prop} [DecidablePred p]
    (hp : ∀ u, p (.inr u)) {α : Type} {oa : OracleComp (unifSpec + (Unit →ₒ Bool)) α}
    (h : IsQueryBoundP oa p 0) : ∃ pa : ProbComp α, liftM pa = oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => exact ⟨pure a, by simp⟩
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at h
    rcases t with n | u
    · choose pa hpa using fun v ↦ ih v (by simpa using h.2 v)
      refine ⟨liftM (unifSpec.query n) >>= pa, ?_⟩
      simp only [liftM_bind, hpa]
      rfl
    · simp [hp u] at h

/-- A zero query budget for a bind is a zero budget for its prefix and for every continuation at a
possible output of the prefix. -/
theorem isQueryBoundP_zero_of_bind {ι : Type} {spec : OracleSpec ι} {p : ι → Prop}
    [DecidablePred p] {α β : Type} {oa : OracleComp spec α} {f : α → OracleComp spec β}
    (h : IsQueryBoundP (oa >>= f) p 0) :
    IsQueryBoundP oa p 0 ∧ ∀ x ∈ support oa, IsQueryBoundP (f x) p 0 := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    rw [pure_bind] at h
    refine ⟨isQueryBoundP_pure _ _ _, fun x hx ↦ ?_⟩
    rw [support_pure, Set.mem_singleton_iff] at hx
    exact hx ▸ h
  | query_bind t k ih =>
    rw [bind_assoc, isQueryBoundP_query_bind_iff] at h
    have hk (u : spec.Range t) : IsQueryBoundP (k u >>= f) p 0 := by
      simpa using h.2 u
    refine ⟨(isQueryBoundP_query_bind_iff _ _ _ _).2 ⟨h.1, fun u ↦ ?_⟩, fun x hx ↦ ?_⟩
    · simpa using (ih u (hk u)).1
    · obtain ⟨u, -, hx⟩ := (mem_support_bind_iff _ _ _).1 hx
      exact (ih u (hk u)).2 x hx

/-- `fixedOracleImpl H` answers the oracle query at `()` with `H ()`. -/
theorem fixedOracleImpl_inr (H : Unit → Bool) :
    fixedOracleImpl H (.inr ()) = (pure (H ()) : ProbComp Bool) :=
  rfl

/-- Against the lazily sampled random oracle, a computation that cannot return `true` against any
fixed oracle function returns `true` with probability zero. -/
theorem rom_evalDist_true_eq_zero {oa : OracleComp (unifSpec + (Unit →ₒ Bool)) Bool}
    (h : ∀ H : Unit → Bool, true ∉ support (simulateQ (fixedOracleImpl H) oa)) :
    (ProbCompRuntime.rom (Unit →ₒ Bool)).evalDist oa {true} = 0 := by
  rw [ProbCompRuntime.rom_evalDist]
  by_contra hne
  have hmem : true ∈ support ((simulateQ (Unit →ₒ Bool).romImpl oa).run' ∅) :=
    (OracleComp.mem_support_iff_evalDist_singleton_pos _ _).2 (pos_iff_ne_zero.2 hne)
  rw [StateT.run'_eq, support_map] at hmem
  obtain ⟨⟨b, s⟩, hbs, hb⟩ := hmem
  obtain ⟨f, -, hf⟩ :=
    (exists_agreesWithFn_mem_support_simulateQ_unifFwdAnswerImpl_iff _ ∅ b).mpr ⟨s, hbs⟩
  exact h (fun x ↦ f x) (by rw [fixedOracleImpl_eq_unifFwdAnswerImpl]; exact hb ▸ hf)

/-- Against the lazily sampled random oracle, a computation that returns only `true` against every
fixed oracle function returns `true` with probability one. -/
theorem rom_evalDist_true_eq_one {oa : OracleComp (unifSpec + (Unit →ₒ Bool)) Bool}
    (h : ∀ H : Unit → Bool, ∀ x ∈ support (simulateQ (fixedOracleImpl H) oa), x = true) :
    (ProbCompRuntime.rom (Unit →ₒ Bool)).evalDist oa {true} = 1 := by
  rw [ProbCompRuntime.rom_evalDist, ← Set.ofPred_eq_eq_singleton,
    evalDist_apply_setOf_simulateQ_romImpl_run'_eq_one_iff]
  intro f _
  rw [OracleComp.evalDist_apply_setOf_eq_one_iff_forall_mem_support,
    ← fixedOracleImpl_eq_unifFwdAnswerImpl]
  exact h _

/-- A computation that makes no query to the oracle runs against the lazily sampled random oracle
independently of the cache. -/
theorem run'_simulateQ_romImpl_of_isQueryBoundP_zero {p : ℕ ⊕ Unit → Prop} [DecidablePred p]
    (hp : ∀ u, p (.inr u)) {α : Type} {oa : OracleComp (unifSpec + (Unit →ₒ Bool)) α}
    (h : IsQueryBoundP oa p 0) (s : (Unit →ₒ Bool).QueryCache) :
    (simulateQ (Unit →ₒ Bool).romImpl oa).run' s =
      (simulateQ (Unit →ₒ Bool).romImpl oa).run' ∅ := by
  obtain ⟨pa, rfl⟩ := exists_liftM_eq_of_isQueryBoundP_zero hp h
  simp [StateT.run'_eq, OracleSpec.simulateQ_romImpl_liftM_run]

/-- From the empty cache, the lazily sampled random oracle answers the query at `()` uniformly, and
a continuation that makes no further oracle query runs as from the empty cache. -/
theorem run'_simulateQ_romImpl_query_bind {p : ℕ ⊕ Unit → Prop} [DecidablePred p]
    (hp : ∀ u, p (.inr u)) {β : Type} {k : Bool → OracleComp (unifSpec + (Unit →ₒ Bool)) β}
    (hk : ∀ r, IsQueryBoundP (k r) p 0) :
    (simulateQ (Unit →ₒ Bool).romImpl
        (liftM ((unifSpec + (Unit →ₒ Bool)).query (.inr ())) >>= k)).run' ∅ =
      ($ᵗ Bool : ProbComp Bool) >>= fun r ↦ (simulateQ (Unit →ₒ Bool).romImpl (k r)).run' ∅ := by
  simp only [add_apply_inr, simulateQ_bind, simulateQ_query, OracleQuery.input_query,
    OracleQuery.cont_query, QueryImpl.add_apply_inr, QueryImpl.withCaching_apply,
    uniformSampleImpl_apply, map_bind, id_map, bind_assoc, StateT.run'_eq, StateT.run_bind,
    StateT.run_get, pure_bind, QueryCache.empty_apply, StateT.run_monadLift, monadLift_self,
    bind_pure_comp, StateT.run_modifyGet, Functor.map_map, bind_map_left]
  refine bind_congr fun r ↦ ?_
  simpa [StateT.run'_eq] using run'_simulateQ_romImpl_of_isQueryBoundP_zero hp (hk r) _

/-- A uniform bit masked with a fixed bit is a uniform bit. -/
theorem uniformSample_bind_xor_evalDistEq {β : Type} (a : Bool) (g : Bool → ProbComp β) :
    (($ᵗ Bool : ProbComp Bool) >>= fun r ↦ g (a ^^ r)) =ᵈ ($ᵗ Bool : ProbComp Bool) >>= g := by
  have hinv : Function.Involutive (a ^^ ·) := fun r ↦ by cases a <;> cases r <;> rfl
  rw [show (($ᵗ Bool : ProbComp Bool) >>= fun r ↦ g (a ^^ r)) =
      ((a ^^ ·) <$> ($ᵗ Bool : ProbComp Bool)) >>= g by simp [map_eq_bind_pure_comp]]
  exact EvalDistEq.bind_left
    (SampleableType.map_uniformSample_evalDistEq_of_bijective hinv.bijective) g

/-- Masks the message bit with the oracle's answer at `()`; the check queries the oracle again and
accepts the claimed value exactly when it unmasks the commitment. -/
def pad : VectorCommitment Unit Bool Bool Bool Unit Unit 1 where
  commit m := do
    let r ← (unifSpec + (Unit →ₒ Bool)).query (.inr ())
    pure (m 0 ^^ r, ())
  opening _ _ := pure ()
  check cm ans _ := do
    let r ← (unifSpec + (Unit →ₒ Bool)).query (.inr ())
    pure (decide (∀ a, ans 0 = some a → cm = (a ^^ r)))

/-- Against an adversary that makes no oracle query, the commitment of `pad` is a one-time pad:
the two worlds have the same distribution, whatever the opened positions. -/
theorem pad_twoMessageHidingAdvantage_eq_zero
    {adversary : TwoMessageHidingAdversary Unit Bool Bool Bool Unit 1}
    (h : adversary.MakesAtMostQueries 0) : pad.twoMessageHidingAdvantage adversary = 0 := by
  obtain ⟨pc, hpc⟩ :=
    exists_liftM_eq_of_isQueryBoundP_zero (fun _ ↦ rfl) (isQueryBoundP_zero_of_bind (h false ())).1
  have key (b : Bool) :
      (simulateQ (Unit →ₒ Bool).romImpl (pad.twoMessageHidingExperiment adversary b)).run' ∅ =ᵈ
        pc >>= fun c ↦
          if PartialVec.restrict c.1 c.2.2.1 = PartialVec.restrict c.2.1 c.2.2.1 then
            ($ᵗ Bool : ProbComp Bool) >>= fun r ↦
              (simulateQ (Unit →ₒ Bool).romImpl (adversary.distinguish c.2.2.2 r ())).run' ∅
          else ($ᵗ Bool : ProbComp Bool) >>= fun _ ↦ pure false := by
    rw [twoMessageHidingExperiment, ← hpc, simulateQ_bind, roSim.run'_liftM_bind]
    refine EvalDistEq.bind_congr_of_support pc fun c hc ↦ ?_
    obtain ⟨m₀, m₁, Q, st⟩ := c
    have hc' : (m₀, m₁, Q, st) ∈ support adversary.choose := by
      rwa [← hpc, ← OracleComp.liftComp_eq_liftM, OracleComp.support_liftComp]
    have hd (cm : Bool) := (isQueryBoundP_zero_of_bind (h cm ())).2 _ hc'
    by_cases hag : PartialVec.restrict m₀ Q = PartialVec.restrict m₁ Q
    · have hL := run'_simulateQ_romImpl_query_bind (fun _ ↦ rfl) (k := fun r ↦
        adversary.distinguish st ((if b then m₁ else m₀) 0 ^^ r) ()) fun r ↦ hd _
      convert hL ▸ uniformSample_bind_xor_evalDistEq ((if b then m₁ else m₀) 0)
        fun r ↦ (simulateQ (Unit →ₒ Bool).romImpl (adversary.distinguish st r ())).run' ∅ using 2
      · simp [hag, pad]
      · simp [hag]
    · simp [hag, pad]
  rw [twoMessageHidingAdvantage_eq, ProbCompRuntime.rom_evalDist, ProbCompRuntime.rom_evalDist,
    (key true).evalDist_eq, (key false).evalDist_eq, ENNReal.absDiff_self]

/-- `pad` is two-message hiding with error `0` against adversaries that make no oracle query, at
every opening size. -/
theorem pad_twoMessageHiding (q : ℕ) : pad.TwoMessageHiding 0 q 0 :=
  fun _ h _ ↦ (pad_twoMessageHidingAdvantage_eq_zero h).le

/-- Chooses two different messages, opens nothing, queries the oracle at `()` and unmasks the
commitment. -/
def unmasker : TwoMessageHidingAdversary Unit Bool Bool Bool Unit 1 where
  State := Unit
  choose := pure (fun _ ↦ false, fun _ ↦ true, ∅, ())
  distinguish _ cm _ := do
    let r ← (unifSpec + (Unit →ₒ Bool)).query (.inr ())
    pure (cm ^^ r)

/-- The unmasker makes one oracle query. -/
theorem unmasker_makesAtMostQueries_one : unmasker.MakesAtMostQueries 1 := by
  intro cm pf
  simp [unmasker]

/-- The unmasker opens no positions. -/
theorem unmasker_opensExactly_zero : unmasker.OpensExactly 0 := by
  intro c hc
  simp only [unmasker, support_pure] at hc
  subst hc
  rfl

/-- The unmasker reads the world bit: `pad` gives it advantage one. -/
theorem pad_twoMessageHidingAdvantage_unmasker : pad.twoMessageHidingAdvantage unmasker = 1 := by
  have agree : PartialVec.restrict (fun _ : Fin 1 ↦ false) ∅ =
      PartialVec.restrict (fun _ ↦ true) ∅ := by
    funext i
    simp [PartialVec.restrict_apply]
  rw [twoMessageHidingAdvantage_eq, rom_evalDist_true_eq_one fun H x hx ↦ ?_,
    rom_evalDist_true_eq_zero fun H hx ↦ ?_]
  · simp
  · simp [twoMessageHidingExperiment, pad, unmasker, fixedOracleImpl_inr,
      agree] at hx
  · simpa [twoMessageHidingExperiment, pad, unmasker, fixedOracleImpl_inr,
      agree] using hx

/-- `pad` is not two-message hiding below error one against adversaries that make one oracle
query, so the query budget matters. -/
theorem not_pad_twoMessageHiding {ε : ENNReal} (hε : ε < 1) : ¬ pad.TwoMessageHiding 1 0 ε :=
  fun h ↦ hε.not_ge (pad_twoMessageHidingAdvantage_unmasker ▸
    h unmasker unmasker_makesAtMostQueries_one unmasker_opensExactly_zero)

/-- `pad` is position binding with advantage zero against every adversary: both checks read the
same oracle answer, so two accepted openings of one commitment agree. -/
theorem pad_positionBindingAdvantage
    (adversary : PositionBindingAdversary Unit Bool Bool Bool Unit 1) :
    pad.positionBindingAdvantage adversary = 0 := by
  rw [positionBindingAdvantage_def]
  refine rom_evalDist_true_eq_zero fun H hmem ↦ ?_
  rw [positionBindingExperiment, simulateQ_bind, mem_support_bind_iff] at hmem
  obtain ⟨⟨cm, ⟨a₁, pf₁⟩, a₂, pf₂⟩, -, hmem⟩ := hmem
  by_cases hc : PartialVec.Conflict a₁ a₂
  · obtain ⟨q, x, y, hx, hy, hxy⟩ := hc
    obtain rfl : q = 0 := Subsingleton.elim _ _
    simp [PartialVec.Conflict, pad, fixedOracleImpl_inr, hx, hy] at hmem
    cases x <;> cases y <;> cases cm <;> cases H () <;> simp_all
  · simp [hc] at hmem

end Pad

/-! ## The salted Merkle commitment -/

section SaltedMerkle

variable {X Y Salt Msg : Type} [DecidableEq X] [DecidableEq Y] [SampleableType Y]
  [SampleableType Salt] [DecidableEq Msg]
  (enc : MerkleTreeHashing.QueryEncoding X Unit Unit (Msg × Salt) Y) (d : ℕ)

/-- The salted Merkle commitment accepts every honest opening with probability one under the
lazily sampled random oracle, the oracle of its binding and hiding advantages. -/
example (msg : Fin (2 ^ d) → Msg) (Q : Finset (Fin (2 ^ d))) :
    (ProbCompRuntime.rom (X →ₒ Y)).evalDist
      ((SaltedMerkle.scheme enc d).toVectorCommitment.completenessExp msg Q) {true} = 1 :=
  (SaltedMerkle.perfectlyComplete enc d).perfectlyCompleteForAll.evalDist_rom_completenessExp_eq_one
    msg Q

/-- The same holds for a random oracle programmed by an initial cache. -/
example (cache : (X →ₒ Y).QueryCache) (msg : Fin (2 ^ d) → Msg) (Q : Finset (Fin (2 ^ d))) :
    (ProbCompRuntime.rom (X →ₒ Y) cache).evalDist
      ((SaltedMerkle.scheme enc d).toVectorCommitment.completenessExp msg Q) {true} = 1 :=
  (SaltedMerkle.perfectlyComplete enc d).perfectlyCompleteForAll.evalDist_rom_completenessExp_eq_one
    msg Q

/-- Position binding can be stated for the salted Merkle commitment. -/
noncomputable example
    (adversary : PositionBindingAdversary X Y Msg Y (SaltedMerkle.Pf Y Salt d) (2 ^ d)) : ENNReal :=
  (SaltedMerkle.scheme enc d).toVectorCommitment.positionBindingAdvantage adversary

/-- Two-message hiding can be stated for the salted Merkle commitment. -/
noncomputable example
    (adversary : TwoMessageHidingAdversary X Y Msg Y (SaltedMerkle.Pf Y Salt d) (2 ^ d)) :
    ENNReal :=
  (SaltedMerkle.scheme enc d).toVectorCommitment.twoMessageHidingAdvantage adversary

end SaltedMerkle

end VectorCommitmentTest
