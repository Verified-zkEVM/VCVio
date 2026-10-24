/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.StalledRun
public import HashSig.SLHDSA.SHAKE128s.Proof.TableBlind
public import HashSig.SLHDSA.SHAKE128s.Proof.RedrawCell
public import HashSig.SLHDSA.SHAKE128s.Proof.SecretGuessCharge
public import HashSig.SLHDSA.SHAKE128s.Proof.SignedWatch
import VCVio.OracleComp.EvalDist.Sum

/-!
# The stall-and-redraw charge, at any oracle spec and any state

`prob_sensitive_le` charges a run one unit of `2 ^ -128` per probe aiming at a cell, by stalling
the run at the cell's release, redrawing the cell after the stalled run, and weighing the
redrawn cell by the probes aiming at it. It is stated for an arbitrary oracle spec and handler
state.

What a handler has to supply is three facts, each a property of one step:

* it **files** what it records: a step appends entries, each beside the snapshot `now` of the
  state it started from (`hfiles`);
* availability only grows along a step (`hmono`);
* it is **blind** to a cell while that cell is unavailable (`hblind`), and whether a cell is
  unavailable is itself blind to that cell (`hunavail`).

The conclusion charges the event that some entry of the record is sensitive — a canonical input
of a node whose staked cell was unavailable when the entry was filed, carrying that cell's value
— at the **expected** number of entries that locate a node, over `2 ^ 128`. It stops at an
expectation so that the charge adds pathwise with any other charge taken in the same game.

The three steps, for one cell:

1. **Flag** (`flagged`). The event is the final value of a sticky flag that a step raises when it
   files a charged entry. A step at a state where the cell is available files nothing charged,
   so the flag is quiet there.
2. **Stall** (`StalledRun.probEvent_flag_stalled_eq`). A run whose flag can no longer move may
   be stopped where it is, and the stalled run is blind to the cell for its whole length.
3. **Redraw** (`RedrawCell.evalDist_redraw_coordinate`). A run blind to a cell may have that
   cell drawn after it, and against a fresh cell each entry aiming at it is one guess.

Stalling leaves the expected number of aiming entries alone too, for the same reason it leaves
the flag alone, so the weights are taken under the real run.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.BlindCharge

open CanonicalGraph SensitiveQuery

variable {ι : Type} {spec : OracleSpec ι} {σ τ K : Type}

/-! ## Running a handler through a projection of its state -/

/-- **A handler that projects onto another runs onto it.** -/
theorem run_simulateQ_map_proj (impl : QueryImpl spec (StateT σ ProbComp))
    (impl' : QueryImpl spec (StateT τ ProbComp)) (f : σ → τ)
    (h : ∀ (t : spec.Domain) (s : σ),
      (fun z => (z.1, f z.2)) <$> (impl t).run s = (impl' t).run (f s))
    {α : Type} (oa : OracleComp spec α) (s : σ) :
    (fun z => (z.1, f z.2)) <$> (simulateQ impl oa).run s =
      (simulateQ impl' oa).run (f s) := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure value => simp
  | query_bind t next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
    rw [← h t s, bind_map_left]
    exact congrArg _ (funext fun z => ih z.1 z.2)

/-- An event read through a projection is the event of the projected run. -/
theorem probEvent_proj (impl : QueryImpl spec (StateT σ ProbComp))
    (impl' : QueryImpl spec (StateT τ ProbComp)) (f : σ → τ)
    (h : ∀ (t : spec.Domain) (s : σ),
      (fun z => (z.1, f z.2)) <$> (impl t).run s = (impl' t).run (f s))
    {α : Type} (oa : OracleComp spec α) (s : σ) (event : α × τ → Prop) :
    Pr{let z ← (simulateQ impl oa).run s}[event (z.1, f z.2)] =
      Pr{let x ← (simulateQ impl' oa).run (f s)}[event x] := by
  rw [← run_simulateQ_map_proj impl impl' f h oa s, prEvent_map]

/-- An expectation read through a projection is the expectation of the projected run. -/
theorem expect_proj (impl : QueryImpl spec (StateT σ ProbComp))
    (impl' : QueryImpl spec (StateT τ ProbComp)) (f : σ → τ)
    (h : ∀ (t : spec.Domain) (s : σ),
      (fun z => (z.1, f z.2)) <$> (impl t).run s = (impl' t).run (f s))
    {α : Type} (oa : OracleComp spec α) (s : σ) (weight : α × τ → ℝ≥0∞) :
    (∑' z, Pr{let x ← (simulateQ impl oa).run s}[x = z] * weight (z.1, f z.2)) =
      ∑' z, Pr{let x ← (simulateQ impl' oa).run (f s)}[x = z] * weight z := by
  rw [← run_simulateQ_map_proj impl impl' f h oa s, tsum_prEvent_map_mul]

/-! ## Filing, and the flag a filing raises -/

section Flag

variable (record : σ → List (Bytes × K)) (now : σ → K)

/-- **A handler files what it records**: a step appends entries, each beside the snapshot of the
state it started from. -/
def Files (impl : QueryImpl spec (StateT σ ProbComp)) : Prop :=
  ∀ (t : spec.Domain) (s : σ), ∀ z ∈ support ((impl t).run s),
    ∃ inputs : List Bytes, record z.2 = record s ++ inputs.map fun input => (input, now s)

open scoped Classical in
/-- The flag after a step from `p` to a state `next`: raised when the step filed a charged entry. -/
noncomputable def raise (charged : Bytes × K → Prop) (p : σ × Bool) (next : σ) : Bool :=
  p.2 || decide (∃ entry ∈ (record next).drop (record p.1).length, charged entry)

/-- The flag is raised exactly when it was up or a newly filed entry is charged. -/
theorem raise_iff (charged : Bytes × K → Prop) (p : σ × Bool) (next : σ) :
    raise record charged p next = true ↔
      p.2 = true ∨ ∃ entry ∈ (record next).drop (record p.1).length, charged entry := by
  classical
  rw [raise, Bool.or_eq_true, decide_eq_true_iff]

/-- The handler with a sticky flag, raised when a step files an entry that is charged. -/
noncomputable def flagged (charged : Bytes × K → Prop) (impl : QueryImpl spec (StateT σ ProbComp)) :
    QueryImpl spec (StateT (σ × Bool) ProbComp) :=
  fun t p => (fun z => (z.1, (z.2, raise record charged p z.2))) <$> (impl t).run p.1

/-- One step of the flagged handler runs the handler and updates the flag. -/
theorem flagged_run (charged : Bytes × K → Prop) (impl : QueryImpl spec (StateT σ ProbComp))
    (t : spec.Domain) (p : σ × Bool) :
    ((flagged record charged impl) t).run p =
      (fun z => (z.1, (z.2, raise record charged p z.2))) <$> (impl t).run p.1 := rfl

/-- Forgetting the flag recovers the underlying handler's step. -/
theorem flagged_proj (charged : Bytes × K → Prop) (impl : QueryImpl spec (StateT σ ProbComp))
    (t : spec.Domain) (p : σ × Bool) :
    (fun z => (z.1, z.2.1)) <$> ((flagged record charged impl) t).run p = (impl t).run p.1 := by
  rw [flagged_run, Functor.map_map]
  exact id_map _

/-- A supported step of the flagged handler is a supported step of the handler. -/
theorem mem_support_flagged (charged : Bytes × K → Prop) (impl : QueryImpl spec (StateT σ ProbComp))
    (t : spec.Domain) (p : σ × Bool) (z : spec.Range t × (σ × Bool))
    (hz : z ∈ support (((flagged record charged impl) t).run p)) :
    ∃ w ∈ support ((impl t).run p.1), z = (w.1, (w.2, raise record charged p w.2)) := by
  rw [flagged_run, support_map] at hz
  obtain ⟨w, hw, hz⟩ := hz
  exact ⟨w, hw, hz.symm⟩

/-- **The flag is the record's verdict**, along a run that files. -/
theorem flag_iff (charged : Bytes × K → Prop) (impl : QueryImpl spec (StateT σ ProbComp))
    (hfiles : Files record now impl) {α : Type} (oa : OracleComp spec α) (s : σ)
    (hs : ¬ ∃ entry ∈ record s, charged entry) :
    ∀ z ∈ support ((simulateQ (flagged record charged impl) oa).run (s, false)),
      (z.2.2 = true ↔ ∃ entry ∈ record z.2.1, charged entry) := by
  classical
  have hinv := SignedWatch.run_invariant (flagged record charged impl)
    (fun p : σ × Bool => (p.2 = true ↔ ∃ entry ∈ record p.1, charged entry))
    (fun t p hp z hz => by
      obtain ⟨w, hw, rfl⟩ := mem_support_flagged record charged impl t p z hz
      obtain ⟨inputs, hrecord⟩ := hfiles t p.1 w hw
      dsimp only
      rw [raise_iff, hrecord, List.drop_left, hp]
      constructor
      · rintro (⟨entry, hentry, hcharged⟩ | ⟨entry, hentry, hcharged⟩)
        · exact ⟨entry, List.mem_append_left _ hentry, hcharged⟩
        · exact ⟨entry, List.mem_append_right _ hentry, hcharged⟩
      · rintro ⟨entry, hentry, hcharged⟩
        rcases List.mem_append.mp hentry with hold | hnew
        · exact Or.inl ⟨entry, hold, hcharged⟩
        · exact Or.inr ⟨entry, hnew, hcharged⟩)
    oa (s, false) (by simpa using hs)
  exact hinv

/-- **The record's verdict is the flagged run's flag.** -/
theorem probEvent_record_eq_flag (charged : Bytes × K → Prop)
    (impl : QueryImpl spec (StateT σ ProbComp)) (hfiles : Files record now impl)
    {α : Type} (oa : OracleComp spec α) (s : σ) (hs : ¬ ∃ entry ∈ record s, charged entry) :
    Pr{let z ← (simulateQ impl oa).run s}[∃ entry ∈ record z.2, charged entry] =
      Pr{let z ← (simulateQ (flagged record charged impl) oa).run (s, false)}[z.2.2 = true] := by
  refine (probEvent_proj (flagged record charged impl) impl Prod.fst
    (fun t p => flagged_proj record charged impl t p) oa (s, false)
    (fun z => ∃ entry ∈ record z.2, charged entry)).symm.trans ?_
  exact (prEvent_congr_of_support _ _ _
    fun z hz => flag_iff record now charged impl hfiles oa s hs z hz).symm

/-! ## Stalling a run that files -/

open scoped Classical in
/-- The handler stalled: once frozen, every query is answered by `stall` and nothing moves. -/
noncomputable def stalledFree (impl : QueryImpl spec (StateT σ ProbComp)) (Frozen : σ → Prop)
    (stall : (t : spec.Domain) → spec.Range t) : QueryImpl spec (StateT σ ProbComp) :=
  fun t s => if Frozen s then pure (stall t, s) else (impl t).run s

open scoped Classical in
/-- One step of the stalled handler: the stall answer when frozen, else the handler. -/
theorem stalledFree_run (impl : QueryImpl spec (StateT σ ProbComp)) (Frozen : σ → Prop)
    (stall : (t : spec.Domain) → spec.Range t) (t : spec.Domain) (s : σ) :
    ((stalledFree impl Frozen stall) t).run s =
      if Frozen s then pure (stall t, s) else (impl t).run s := rfl

/-- Stalling a handler that files keeps it a handler that files. -/
theorem files_stalledFree (impl : QueryImpl spec (StateT σ ProbComp))
    (hfiles : Files record now impl) (Frozen : σ → Prop)
    (stall : (t : spec.Domain) → spec.Range t) :
    Files record now (stalledFree impl Frozen stall) := by
  classical
  intro t s z hz
  rw [stalledFree_run] at hz
  split_ifs at hz with hfrozen
  · rw [support_pure, Set.mem_singleton_iff] at hz
    exact ⟨[], by rw [hz]; simp⟩
  · exact hfiles t s z hz

/-- **Stalling the flagged handler is flagging the stalled one.** -/
theorem stalled_flagged (charged : Bytes × K → Prop) (impl : QueryImpl spec (StateT σ ProbComp))
    (Frozen : σ → Prop) (stall : (t : spec.Domain) → spec.Range t) :
    StalledRun.stalled (flagged record charged impl) Frozen stall =
      flagged record charged (stalledFree impl Frozen stall) := by
  classical
  funext t p
  change (StalledRun.stalled (flagged record charged impl) Frozen stall t).run p =
    ((flagged record charged (stalledFree impl Frozen stall)) t).run p
  by_cases hp : Frozen p.1
  · rw [StalledRun.stalled_run_of_frozen _ Frozen stall t p hp, flagged_run, stalledFree_run,
      ite_eq_left hp, map_pure]
    congr
    rcases p with ⟨inner, flag⟩
    cases flag <;> simp [raise]
  · rw [StalledRun.stalled_run_of_not_frozen _ Frozen stall t p hp, flagged_run, flagged_run,
      stalledFree_run, ite_eq_right hp]

/-- **Stalling leaves the record's verdict alone**, once nothing filed can be charged. -/
theorem probEvent_record_stalled (charged : Bytes × K → Prop)
    (impl : QueryImpl spec (StateT σ ProbComp))
    (hfiles : Files record now impl) (Frozen : σ → Prop)
    (stall : (t : spec.Domain) → spec.Range t)
    (hfrozen : ∀ (t : spec.Domain) (s : σ), Frozen s → ∀ z ∈ support ((impl t).run s), Frozen z.2)
    (hquiet : ∀ s : σ, Frozen s → ∀ input : Bytes, ¬ charged (input, now s))
    {α : Type} (oa : OracleComp spec α) (s : σ) (hs : ¬ ∃ entry ∈ record s, charged entry) :
    Pr{let z ← (simulateQ impl oa).run s}[∃ entry ∈ record z.2, charged entry] =
      Pr{let z ← (simulateQ (stalledFree impl Frozen stall) oa).run s}[
        ∃ entry ∈ record z.2, charged entry] := by
  classical
  rw [probEvent_record_eq_flag record now charged impl hfiles oa s hs,
    probEvent_record_eq_flag record now charged _ (files_stalledFree record now impl hfiles
      Frozen stall) oa s hs, ← stalled_flagged]
  refine StalledRun.probEvent_flag_stalled_eq _ Frozen stall
    (fun t p hp z hz => ?_)
    (fun t p hp z hz => ?_) oa (s, false)
  · obtain ⟨w, hw, rfl⟩ := mem_support_flagged record charged impl t p z hz
    exact hfrozen t p.1 hp w hw
  · obtain ⟨w, hw, rfl⟩ := mem_support_flagged record charged impl t p z hz
    obtain ⟨inputs, hrecord⟩ := hfiles t p.1 w hw
    dsimp only
    cases hflag : raise record charged p w.2
    · rw [raise, Bool.or_eq_false_iff] at hflag
      exact hflag.1.symm
    · rcases (raise_iff record charged p w.2).mp hflag with hold | ⟨entry, hentry, hcharged⟩
      · exact hold.symm
      · rw [hrecord, List.drop_left] at hentry
        obtain ⟨input, -, rfl⟩ := List.mem_map.mp hentry
        exact absurd hcharged (hquiet p.1 hp input)

open scoped Classical in
/-- **Stalling leaves the expected count alone**, once nothing filed can be counted. -/
theorem expect_count_stalled (count : Bytes × K → Prop)
    (impl : QueryImpl spec (StateT σ ProbComp))
    (hfiles : Files record now impl) (Frozen : σ → Prop)
    (stall : (t : spec.Domain) → spec.Range t)
    (hfrozen : ∀ (t : spec.Domain) (s : σ), Frozen s → ∀ z ∈ support ((impl t).run s), Frozen z.2)
    (hquiet : ∀ s : σ, Frozen s → ∀ input : Bytes, ¬ count (input, now s))
    {α : Type} (oa : OracleComp spec α) (s : σ) :
    (∑' z, Pr{let x ← (simulateQ impl oa).run s}[x = z] *
        (((record z.2).countP fun entry => decide (count entry) : Nat) : ℝ≥0∞)) =
      ∑' z, Pr{let x ← (simulateQ (stalledFree impl Frozen stall) oa).run s}[x = z] *
        (((record z.2).countP fun entry => decide (count entry) : Nat) : ℝ≥0∞) := by
  classical
  have hleft := expect_proj (flagged record count impl) impl Prod.fst
    (fun t p => flagged_proj record count impl t p) oa (s, false)
    (fun z => (((record z.2).countP fun entry => decide (count entry) : Nat) : ℝ≥0∞))
  have hright := expect_proj (flagged record count (stalledFree impl Frozen stall))
    (stalledFree impl Frozen stall) Prod.fst
    (fun t p => flagged_proj record count _ t p) oa (s, false)
    (fun z => (((record z.2).countP fun entry => decide (count entry) : Nat) : ℝ≥0∞))
  dsimp only at hleft hright
  rw [← hleft, ← hright, ← stalled_flagged]
  refine StalledRun.expectation_stalled_eq _ Frozen stall
    (fun p => (((record p.1).countP fun entry => decide (count entry) : Nat) : ℝ≥0∞))
    (fun t p hp z hz => ?_)
    (fun t p hp z hz => ?_) oa (s, false)
  · obtain ⟨w, hw, rfl⟩ := mem_support_flagged record count impl t p z hz
    exact hfrozen t p.1 hp w hw
  · obtain ⟨w, hw, rfl⟩ := mem_support_flagged record count impl t p z hz
    obtain ⟨inputs, hrecord⟩ := hfiles t p.1 w hw
    dsimp only
    rw [hrecord, List.countP_append]
    have hzero : (inputs.map fun input => (input, now p.1)).countP
        (fun entry => decide (count entry)) = 0 := by
      rw [List.countP_eq_zero]
      intro entry hentry
      obtain ⟨input, -, rfl⟩ := List.mem_map.mp hentry
      simpa using hquiet p.1 hp input
    rw [hzero, Nat.add_zero]

end Flag

/-! ## Expectations -/

/-- The expectation of a nonnegative quantity. -/
noncomputable def ex {β : Type} (mx : ProbComp β) (f : β → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' x, Pr{let y ← mx}[y = x] * f x

/-- The expectation over a bind is the iterated expectation. -/
theorem ex_bind {β γ : Type} (mx : ProbComp β) (g : β → ProbComp γ) (f : γ → ℝ≥0∞) :
    ex (mx >>= g) f = ex mx fun x => ex (g x) f :=
  tsum_prEvent_bind_mul mx g f

/-- The expectation over a mapped computation is the expectation of the composite. -/
theorem ex_map {β γ : Type} (mx : ProbComp β) (g : β → γ) (f : γ → ℝ≥0∞) :
    ex (g <$> mx) f = ex mx (f ∘ g) :=
  tsum_prEvent_map_mul mx g f

/-- The expectation is monotone in the integrand. -/
theorem ex_mono {β : Type} (mx : ProbComp β) {f g : β → ℝ≥0∞} (h : ∀ x, f x ≤ g x) :
    ex mx f ≤ ex mx g :=
  ENNReal.tsum_le_tsum fun x => mul_le_mul' le_rfl (h x)

/-- The expectation depends only on the integrand's values. -/
theorem ex_congr {β : Type} (mx : ProbComp β) {f g : β → ℝ≥0∞} (h : ∀ x, f x = g x) :
    ex mx f = ex mx g :=
  tsum_congr fun x => by rw [h x]

/-- Dividing the integrand by a constant divides the expectation by it. -/
theorem ex_div_const {β : Type} (mx : ProbComp β) (f : β → ℝ≥0∞) (c : ℝ≥0∞) :
    ex mx (fun x => f x / c) = ex mx f / c := by
  simp only [ex, div_eq_mul_inv, ← mul_assoc]
  exact ENNReal.tsum_mul_right

/-- The probability of an event after a bind is the expected conditional probability. -/
theorem probEvent_eq_ex_bind {β γ : Type} (mx : ProbComp β) (g : β → ProbComp γ)
    (event : γ → Prop) : Pr{let x ← mx >>= g}[event x] = ex mx fun x => Pr{let y ← g x}[event y] :=
  OracleComp.prEvent_bind_eq_tsum mx g event

/-! ## The experiment: a table, auxiliary randomness, and a run at both -/

variable {Aux α : Type}

/-- **The experiment the charge is about.** -/
noncomputable def experiment (auxiliary : ProbComp Aux)
    (run : Cells → Aux → ProbComp (α × σ)) : ProbComp ((α × σ) × Cells × Aux) := do
  let cells ← ($ᵗ Cells : ProbComp Cells)
  let aux ← auxiliary
  let z ← run cells aux
  pure (z, cells, aux)

/-- An event of the experiment, as an iterated expectation over table and randomness. -/
theorem probEvent_experiment (auxiliary : ProbComp Aux) (run : Cells → Aux → ProbComp (α × σ))
    (event : (α × σ) × Cells × Aux → Prop) :
    Pr{let x ← experiment auxiliary run}[event x] =
      ex ($ᵗ Cells : ProbComp Cells) fun cells => ex auxiliary fun aux =>
        Pr{let z ← run cells aux}[event (z, cells, aux)] := by
  rw [experiment, probEvent_eq_ex_bind]
  refine ex_congr _ fun cells => ?_
  rw [probEvent_eq_ex_bind]
  refine ex_congr _ fun aux => ?_
  rw [bind_pure_comp, prEvent_map]

/-- An expectation over the experiment, iterated over table and auxiliary randomness. -/
theorem ex_experiment (auxiliary : ProbComp Aux) (run : Cells → Aux → ProbComp (α × σ))
    (f : (α × σ) × Cells × Aux → ℝ≥0∞) :
    ex (experiment auxiliary run) f =
      ex ($ᵗ Cells : ProbComp Cells) fun cells => ex auxiliary fun aux =>
        ex (run cells aux) fun z => f (z, cells, aux) := by
  rw [experiment, ex_bind]
  refine ex_congr _ fun cells => ?_
  rw [ex_bind]
  refine ex_congr _ fun aux => ?_
  rw [bind_pure_comp, ex_map]
  rfl

/-! ## One entry, one guess at a fresh cell -/

section Redraw

variable {Index Target : Type} (stakes : Stakes Target Index)

/-- An entry **charged against** a cell at a value: the canonical input of a node staking that
cell, filed while the cell was unavailable, carrying that value. -/
def ChargedAt (unavail : K → Index → Prop) (index : Index) (cell : Cell) (entry : Bytes × K) :
    Prop :=
  ∃ node : Target, stakes.stake node = index ∧ unavail entry.2 index ∧
    stakes.inputOf node cell = entry.1

/-- An entry **aiming at** a cell: its address names a node staking that cell, filed while the
cell was unavailable. No cell is read. -/
def AimsAt (unavail : K → Index → Prop) (index : Index) (entry : Bytes × K) : Prop :=
  ∃ node : Target, stakes.stake node = index ∧ unavail entry.2 index ∧
    stakes.locate entry.1 = some node

/-- An entry charged against a cell aims at that cell's index. -/
theorem aimsAt_of_chargedAt (unavail : K → Index → Prop) (index : Index) (cell : Cell)
    (entry : Bytes × K) (hcharged : ChargedAt stakes unavail index cell entry) :
    AimsAt stakes unavail index entry := by
  obtain ⟨node, hstake, hunavail, hinput⟩ := hcharged
  exact ⟨node, hstake, hunavail, by rw [← hinput, stakes.locate_inputOf]⟩

/-- **An entry is one guess at a fresh cell.** -/
theorem prob_chargedAt_le (unavail : K → Index → Prop) (index : Index) (entry : Bytes × K) :
    Pr{let cell ← ($ᵗ Cell : ProbComp Cell)}[ChargedAt stakes unavail index cell entry] ≤
      1 / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  classical
  by_cases h : ∃ value, ChargedAt stakes unavail index value entry
  · obtain ⟨value, node, -, -, hvalue⟩ := h
    refine le_of_le_of_eq (prEvent_mono _ _ (fun cell : Cell => value = cell) ?_)
      (SecretGuessCharge.prob_single_guess value)
    rintro cell ⟨other, -, -, hcell⟩
    have hsame : other = node := by
      have hleft : stakes.locate entry.1 = some other := by rw [← hcell, stakes.locate_inputOf]
      have hright : stakes.locate entry.1 = some node := by rw [← hvalue, stakes.locate_inputOf]
      exact Option.some.inj (hleft.symm.trans hright)
    subst hsame
    exact stakes.inputOf_injective other (hvalue.trans hcell.symm)
  · refine le_of_eq_of_le (b := 0)
      (prEvent_eq_zero_of_forall_not _ _ fun cell hcharged => h ⟨cell, hcharged⟩) (by simp)

open scoped Classical in
/-- **A list of entries against a fresh cell**: one guess per entry aiming at it. -/
theorem prob_list_chargedAt_le (unavail : K → Index → Prop) (index : Index)
    (entries : List (Bytes × K)) :
    Pr{let cell ← ($ᵗ Cell : ProbComp Cell)}[
        ∃ entry ∈ entries, ChargedAt stakes unavail index cell entry] ≤
      ((entries.countP fun entry => decide (AimsAt stakes unavail index entry) : Nat) : ℝ≥0∞) /
        ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  classical
  refine le_trans (prEvent_mono _ _ (fun cell : Cell =>
    ∃ entry ∈ (entries.filter fun entry => decide (AimsAt stakes unavail index entry)).toFinset,
      ChargedAt stakes unavail index cell entry) ?_) ?_
  · rintro cell ⟨entry, hentry, hcharged⟩
    refine ⟨entry, List.mem_toFinset.mpr (List.mem_filter.mpr ⟨hentry, ?_⟩), hcharged⟩
    exact decide_eq_true (aimsAt_of_chargedAt stakes unavail index cell entry hcharged)
  refine le_trans (prEvent_exists_finset_le _ _ _) ?_
  refine le_trans (Finset.sum_le_sum fun entry _ => prob_chargedAt_le stakes unavail index entry) ?_
  rw [Finset.sum_const, nsmul_eq_mul, mul_one_div]
  refine ENNReal.div_le_div_right (Nat.cast_le.mpr ?_) _
  rw [List.countP_eq_length_filter]
  exact List.toFinset_card_le _

end Redraw

/-! ## The charge against one cell -/

section Charge

variable {Target : Type} (stakes : Stakes Target Node)
  (record : σ → List (Bytes × K)) (now : σ → K)

/-- Two tables agreeing off one cell. -/
def AgreeOff (index : Node) (cells other : Cells) : Prop :=
  ∀ node, node ≠ index → cells node = other node

open scoped Classical in
/-- **The charge against one cell**: the chance that some entry is charged against it is at most
the expected number of entries aiming at it, over `2 ^ 128`. -/
theorem prob_index_le (auxiliary : ProbComp Aux)
    (impl : Cells → Aux → QueryImpl spec (StateT σ ProbComp))
    (comp : Cells → Aux → OracleComp spec α) (start : σ) (hstart : record start = [])
    (unavail : Cells → Aux → K → Node → Prop) (index : Node)
    (stall : (t : spec.Domain) → spec.Range t)
    (hfiles : ∀ cells aux, Files record now (impl cells aux))
    (hmono : ∀ cells aux t s, ¬ unavail cells aux (now s) index →
      ∀ z ∈ support ((impl cells aux t).run s), ¬ unavail cells aux (now z.2) index)
    (hblind : ∀ cells other aux, AgreeOff index cells other → ∀ t s,
      unavail cells aux (now s) index → (impl cells aux t).run s =ᵈ (impl other aux t).run s)
    (hunavail : ∀ cells other aux, AgreeOff index cells other → ∀ k,
      unavail cells aux k index ↔ unavail other aux k index)
    (hcomp : ∀ cells other aux, AgreeOff index cells other → comp cells aux = comp other aux) :
    Pr{let w ← experiment auxiliary fun cells aux =>
        (simulateQ (impl cells aux) (comp cells aux)).run start}[∃ entry ∈ record w.1.2,
        ChargedAt stakes (unavail w.2.1 w.2.2) index (w.2.1 index) entry] ≤
      ex (experiment auxiliary fun cells aux =>
          (simulateQ (impl cells aux) (comp cells aux)).run start)
        (fun w => (((record w.1.2).countP fun entry =>
          decide (AimsAt stakes (unavail w.2.1 w.2.2) index entry) : Nat) : ℝ≥0∞)) /
        ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  classical
  let Frozen : Cells → Aux → σ → Prop := fun cells aux s => ¬ unavail cells aux (now s) index
  let stalledRun : Cells → Aux → ProbComp (α × σ) := fun cells aux =>
    (simulateQ (stalledFree (impl cells aux) (Frozen cells aux) stall) (comp cells aux)).run start
  let run' : Cells → Aux → ProbComp ((α × σ) × (K → Prop)) := fun cells aux =>
    (fun z => (z, fun k => unavail cells aux k index)) <$> stalledRun cells aux
  let event' : ((α × σ) × (K → Prop)) × Cell → Prop := fun p =>
    ∃ entry ∈ record p.1.1.2, ChargedAt stakes (fun k _ => p.1.2 k) index p.2 entry
  have hempty : ∀ (charged : Bytes × K → Prop), ¬ ∃ entry ∈ record start, charged entry := by
    intro charged
    rw [hstart]
    simp
  -- Stall at the cell's release: the event does not move.
  have hstalled : Pr{let w ← experiment auxiliary fun cells aux =>
        (simulateQ (impl cells aux) (comp cells aux)).run start}[∃ entry ∈ record w.1.2,
        ChargedAt stakes (unavail w.2.1 w.2.2) index (w.2.1 index) entry] =
      Pr{let w ← experiment auxiliary stalledRun}[∃ entry ∈ record w.1.2,
        ChargedAt stakes (unavail w.2.1 w.2.2) index (w.2.1 index) entry] := by
    rw [probEvent_experiment, probEvent_experiment]
    refine ex_congr _ fun cells => ex_congr _ fun aux => ?_
    exact probEvent_record_stalled record now
      (fun entry => ChargedAt stakes (unavail cells aux) index (cells index) entry)
      (impl cells aux) (hfiles cells aux) (Frozen cells aux) stall
      (fun t s hs z hz => hmono cells aux t s hs z hz)
      (fun s hs input ⟨_, _, hu, _⟩ => hs hu) (comp cells aux) start (hempty _)
  -- The stalled run, with the cell's unavailability carried beside it.
  have hredrawForm : Pr{let w ← experiment auxiliary stalledRun}[∃ entry ∈ record w.1.2,
        ChargedAt stakes (unavail w.2.1 w.2.2) index (w.2.1 index) entry] =
      Pr{let x ← (do
        let cells ← ($ᵗ Cells : ProbComp Cells)
        let aux ← auxiliary
        let result ← run' cells aux
        pure (result, cells index))}[event' x] := by
    rw [probEvent_experiment, probEvent_eq_ex_bind]
    refine ex_congr _ fun cells => ?_
    rw [probEvent_eq_ex_bind]
    refine ex_congr _ fun aux => ?_
    rw [bind_pure_comp, prEvent_map, prEvent_map]
    rfl
  -- The stalled run is blind to the cell.
  have hcongr : ∀ (cells other : Cells) (aux : Aux),
      (∀ node, node ≠ index → cells node = other node) →
        run' cells aux =ᵈ run' other aux := by
    intro cells other aux hagree
    have hU : (fun k => unavail cells aux k index) = (fun k => unavail other aux k index) :=
      funext fun k => propext (hunavail cells other aux hagree k)
    have hrun : stalledRun cells aux =ᵈ stalledRun other aux := by
      change (simulateQ (stalledFree (impl cells aux) (Frozen cells aux) stall)
          (comp cells aux)).run start =ᵈ
        (simulateQ (stalledFree (impl other aux) (Frozen other aux) stall)
          (comp other aux)).run start
      rw [hcomp cells other aux hagree]
      refine TableBlind.evalDist_run_congr_of_step
        (fun table => stalledFree (impl table aux) (Frozen table aux) stall)
        (fun left right => AgreeOff index left right) (fun t st left right hlr => ?_)
        (comp other aux) cells other hagree start
      rw [stalledFree_run, stalledFree_run]
      have hiff : Frozen left aux st ↔ Frozen right aux st :=
        not_congr (hunavail left right aux hlr (now st))
      by_cases hfrozen : Frozen left aux st
      · rw [ite_eq_left hfrozen, ite_eq_left (hiff.mp hfrozen)]
      · rw [ite_eq_right hfrozen, ite_eq_right fun h => hfrozen (hiff.mpr h)]
        exact hblind left right aux hlr t st (not_not.mp hfrozen)
    change (fun z => (z, fun k => unavail cells aux k index)) <$> stalledRun cells aux =ᵈ
      (fun z => (z, fun k => unavail other aux k index)) <$> stalledRun other aux
    rw [hU]
    exact hrun.map _
  -- Redraw the cell after the run, and charge each aiming entry once.
  rw [hstalled, hredrawForm,
    (RedrawCell.evalDist_redraw_coordinate index auxiliary run' hcongr).prEvent_eq event']
  have hbound : Pr{let x ← (do
        let cells ← ($ᵗ Cells : ProbComp Cells)
        let aux ← auxiliary
        let result ← run' cells aux
        let cell ← ($ᵗ Cell : ProbComp Cell)
        pure (result, cell))}[event' x] ≤
      ex ($ᵗ Cells : ProbComp Cells) fun cells => ex auxiliary fun aux =>
        ex (stalledRun cells aux) fun z =>
          (((record z.2).countP fun entry =>
            decide (AimsAt stakes (unavail cells aux) index entry) : Nat) : ℝ≥0∞) /
            ((2 ^ 128 : Nat) : ℝ≥0∞) := by
    rw [probEvent_eq_ex_bind]
    refine ex_mono _ fun cells => ?_
    rw [probEvent_eq_ex_bind]
    refine ex_mono _ fun aux => ?_
    rw [probEvent_eq_ex_bind, ex_map]
    refine ex_mono _ fun z => ?_
    simp only [Function.comp]
    rw [bind_pure_comp, prEvent_map]
    exact prob_list_chargedAt_le stakes (fun k _ => unavail cells aux k index) index (record z.2)
  refine le_trans hbound (le_of_eq ?_)
  rw [ex_experiment, ← ex_div_const]
  refine ex_congr _ fun cells => ?_
  rw [← ex_div_const]
  refine ex_congr _ fun aux => ?_
  rw [ex_div_const]
  congr 1
  exact (expect_count_stalled record now
    (fun entry => AimsAt stakes (unavail cells aux) index entry) (impl cells aux)
    (hfiles cells aux) (Frozen cells aux) stall
    (fun t s hs z hz => hmono cells aux t s hs z hz)
    (fun s hs input ⟨_, _, hu, _⟩ => hs hu) (comp cells aux) start).symm

end Charge

/-! ## Summed over the cells -/

section Sum

variable {Target : Type}

open scoped Classical in
/-- **An entry aims at one cell at most, and only if it locates a node.** -/
theorem sum_countP_aimsAt_le {Index : Type} [Fintype Index] (stakes : Stakes Target Index)
    (unavail : K → Index → Prop) (entries : List (Bytes × K)) :
    ∑ index : Index, entries.countP (fun entry => decide (AimsAt stakes unavail index entry)) ≤
      entries.countP fun entry => (stakes.locate entry.1).isSome := by
  classical
  induction entries with
  | nil => simp
  | cons entry rest ih =>
    simp only [List.countP_cons, Finset.sum_add_distrib]
    refine Nat.add_le_add ih ?_
    cases hlocate : stakes.locate entry.1 with
    | none =>
      refine le_of_eq_of_le (Finset.sum_eq_zero fun index _ => ?_) (Nat.zero_le _)
      rw [ite_eq_right]
      rintro hdecide
      obtain ⟨node, -, -, hnode⟩ := of_decide_eq_true hdecide
      rw [hlocate] at hnode
      cases hnode
    | some node =>
      simp only [Option.isSome_some, ite_true]
      refine le_trans (le_of_eq (Finset.sum_boole _ _)) ?_
      refine Finset.card_le_one.mpr fun first hfirst second hsecond => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq] at hfirst hsecond
      obtain ⟨firstNode, hfirstStake, -, hfirstLocate⟩ := hfirst
      obtain ⟨secondNode, hsecondStake, -, hsecondLocate⟩ := hsecond
      rw [hlocate] at hfirstLocate hsecondLocate
      cases hfirstLocate
      cases hsecondLocate
      rw [← hfirstStake, ← hsecondStake]

variable (stakes : Stakes Target Node) (record : σ → List (Bytes × K)) (now : σ → K)

open scoped Classical in
/-- **The charge**: the chance that some entry of the record is sensitive is at most the
expected number of entries that locate a node, over `2 ^ 128`. -/
theorem prob_sensitive_le (auxiliary : ProbComp Aux)
    (impl : Cells → Aux → QueryImpl spec (StateT σ ProbComp))
    (comp : Cells → Aux → OracleComp spec α) (start : σ) (hstart : record start = [])
    (unavail : Cells → Aux → K → Node → Prop) (stall : (t : spec.Domain) → spec.Range t)
    (Chargeable : Node → Prop)
    (hcharge : ∀ cells aux k index, unavail cells aux k index → Chargeable index)
    (hfiles : ∀ cells aux, Files record now (impl cells aux))
    (hmono : ∀ index, Chargeable index → ∀ cells aux t s, ¬ unavail cells aux (now s) index →
      ∀ z ∈ support ((impl cells aux t).run s), ¬ unavail cells aux (now z.2) index)
    (hblind : ∀ index, Chargeable index → ∀ cells other aux, AgreeOff index cells other →
      ∀ t s, unavail cells aux (now s) index →
        (impl cells aux t).run s =ᵈ (impl other aux t).run s)
    (hunavail : ∀ index, Chargeable index → ∀ cells other aux, AgreeOff index cells other →
      ∀ k, unavail cells aux k index ↔ unavail other aux k index)
    (hcomp : ∀ index, Chargeable index → ∀ cells other aux, AgreeOff index cells other →
      comp cells aux = comp other aux) :
    Pr{let w ← experiment auxiliary fun cells aux =>
        (simulateQ (impl cells aux) (comp cells aux)).run start}[∃ entry ∈ record w.1.2,
        Sensitive stakes (unavail w.2.1 w.2.2) w.2.1 entry.2 entry.1] ≤
      ex (experiment auxiliary fun cells aux =>
          (simulateQ (impl cells aux) (comp cells aux)).run start)
        (fun w => (((record w.1.2).countP fun entry =>
          (stakes.locate entry.1).isSome : Nat) : ℝ≥0∞)) /
        ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  classical
  refine le_trans (prEvent_mono _ _ (fun w => ∃ index ∈ (Finset.univ : Finset Node),
    ∃ entry ∈ record w.1.2, ChargedAt stakes (unavail w.2.1 w.2.2) index (w.2.1 index) entry)
    ?_) ?_
  · rintro w ⟨entry, hentry, node, hunavailable, hinput⟩
    refine ⟨stakes.stake node, ?_, entry, hentry, node, rfl, hunavailable, hinput⟩
    simp
  refine le_trans (prEvent_exists_finset_le _ _ _) ?_
  have hindex : ∀ index : Node,
      Pr{let w ← experiment auxiliary fun cells aux =>
          (simulateQ (impl cells aux) (comp cells aux)).run start}[∃ entry ∈ record w.1.2,
          ChargedAt stakes (unavail w.2.1 w.2.2) index (w.2.1 index) entry] ≤
        ex (experiment auxiliary fun cells aux =>
          (simulateQ (impl cells aux) (comp cells aux)).run start)
          (fun w => (((record w.1.2).countP fun entry =>
          decide (AimsAt stakes (unavail w.2.1 w.2.2) index entry) : Nat) : ℝ≥0∞)) /
          ((2 ^ 128 : Nat) : ℝ≥0∞) := by
    intro index
    by_cases hc : Chargeable index
    · exact prob_index_le stakes record now auxiliary impl comp start hstart unavail index stall
        hfiles (hmono index hc) (hblind index hc) (hunavail index hc) (hcomp index hc)
    · refine le_trans (le_of_eq (prEvent_eq_zero_of_forall_not _ _ ?_)) (by simp)
      rintro w ⟨entry, -, node, -, hunavailable, -⟩
      exact hc (hcharge _ _ _ _ hunavailable)
  refine le_trans (Finset.sum_le_sum fun index _ => hindex index) ?_
  simp only [div_eq_mul_inv, ← Finset.sum_mul]
  refine mul_le_mul' ?_ le_rfl
  unfold ex
  rw [ChargedProbe.sum_tsum_comm]
  refine ENNReal.tsum_le_tsum fun w => ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul' le_rfl ?_
  rw [← Nat.cast_sum]
  exact Nat.cast_le.mpr (sum_countP_aimsAt_le stakes (unavail w.2.1 w.2.2) (record w.1.2))

end Sum

end SlhDsaSecurity.BlindCharge
