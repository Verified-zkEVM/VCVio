/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.Coinductive.PolyTimeClosure
import ToMathlib.Computability.MachineCounting

/-!
# Non-Triviality Certificates for the Polynomial-Time Adversary Model

Acceptance targets for the canonical-boundary machine model: theorems asserting that
the polynomial-time class does **not** contain every function. Their provability is the
model's soundness certificate, and their history is the model's design rationale:

* With the pre-canonicalization model (existential boundary encodings), both statements
  below were **false**: the encoding `enc x := std x ++ block (f x)` caches any `f`
  inside the input representation, whereupon a bundle with `steps = 0`, `initTM` the
  identity machine, `exposeTM` a constant machine, and two small streaming machines
  (a projection and a block extraction) certifies `f` — no machine ever computes `f`.
* With pinned canonical boundaries (`BoundaryData`), the caching channel is closed, and
  the counting/diagonalization argument goes through: an implementing bundle's
  input→output behavior at parameter `n` factors through its four witness string
  functions (machines of at most `descBound`-many states over the fixed `Bool`
  alphabet, composed at most `steps`-many times), of which there are at most
  `2^{O(d log d)}` at size `d`, while there are `2^{2^n}` functions `BitVec n → Bool`;
  a function chosen (classically) to differ from every `2^{n/4}`-sized composite
  behavior defeats every polynomial bundle at large `n`.

The proofs are staged (see `docs/agents/polytime-model.md`): the run-factorization
lemma (the "compiled run": the deterministic run against a fixed handler is an iterate
of the witness string functions), machine counting and normalization to `Fin d` state
spaces, elementary `p.eval n ≤ 2^(n/4)` growth bounds, and the diagonal construction.
The `sorry`s below are those staged proofs' end products, recorded as the model's
falsifiable acceptance criteria rather than smuggled as axioms — nothing downstream
may depend on them.
-/

open OracleSpec Computability

/-! ## Local support: appending a fixed bit on a single-tape machine

The compiled deterministic run inserts the fixed canonical coin answer into the state
encoding before each `update` step. At the canonical coin boundary the query index has
width `0` and the answer `⟨t, r⟩` encodes as the single bit `[r]`, so "insert the fixed
`true` answer" is exactly appending `[true]` to the state encoding. The Cslib base library
provides `idComputer`, `constComputer`, and `tableComputer`, but no combinator appending a
fixed suffix to an *unbounded* string; we supply one here as local support, in the same
`SingleTapeTM` style. -/

namespace Turing.SingleTapeTM

open Turing Relation

/-- Append a fixed symbol `c` at the right end of the input: walk right keeping every
symbol (`inl`), write `c` at the trailing blank and turn around (`inr`), then walk back
left keeping every symbol until falling off the left end, where one right step lands the
head on the first symbol of the output `l ++ [c]`. -/
def snocComputer (c : Bool) : SingleTapeTM Bool where
  State := Unit ⊕ Unit
  q₀ := .inl ()
  tr q h := match q with
    | .inl () => match h with
      | some b => ⟨⟨some b, some .right⟩, some (.inl ())⟩
      | none => ⟨⟨some c, some .left⟩, some (.inr ())⟩
    | .inr () => match h with
      | some b => ⟨⟨some b, some .left⟩, some (.inr ())⟩
      | none => ⟨⟨none, some .right⟩, none⟩

/-- The left stack after the rightward pass has consumed `l` (starting from stack `L`):
each symbol of `l` is pushed on top in turn, so the top is the last symbol of `l`. -/
private def snocPush : StackTape Bool → List Bool → StackTape Bool
  | L, [] => L
  | L, b :: t => snocPush (StackTape.cons (some b) L) t

@[simp] private lemma snocPush_nil (L : StackTape Bool) : snocPush L [] = L := rfl

@[simp] private lemma snocPush_cons (L : StackTape Bool) (b : Bool) (t : List Bool) :
    snocPush L (b :: t) = snocPush (StackTape.cons (some b) L) t := rfl

private lemma stackTape_ext {a b : StackTape Bool} (h : a.toList = b.toList) : a = b := by
  cases a; cases b; cases h; rfl

private lemma snocPush_toList (L : StackTape Bool) (l : List Bool) :
    (snocPush L l).toList = l.reverse.map some ++ L.toList := by
  induction l generalizing L with
  | nil => simp
  | cons b t ih =>
    rw [snocPush_cons, ih (StackTape.cons (some b) L), StackTape.cons_some_toList]
    simp

private lemma mapSome_head (l : List Bool) :
    (StackTape.mapSome l).head = l.head?.map some := by
  cases l <;> rfl

private lemma mapSome_tail (l : List Bool) :
    (StackTape.mapSome l).tail = StackTape.mapSome l.tail := by
  cases l <;> rfl

private lemma mk₁_eq (s : List Bool) :
    (BiTape.mk₁ s : BiTape Bool) =
      ⟨(StackTape.mapSome s).head, ∅, (StackTape.mapSome s).tail⟩ := by
  cases s <;> rfl

/-- Rightward pass: from head over the first of `l` with left stack `L`, reach the trailing
blank with `l` pushed onto `L`, in `l.length` steps. -/
private lemma snocComputer_phaseA (c : Bool) (L : StackTape Bool) : ∀ l : List Bool,
    RelatesInSteps (snocComputer c).TransitionRelation
      ⟨some (.inl ()), ⟨(StackTape.mapSome l).head, L, (StackTape.mapSome l).tail⟩⟩
      ⟨some (.inl ()), ⟨none, snocPush L l, ∅⟩⟩ l.length := by
  intro l
  induction l generalizing L with
  | nil => exact .refl _
  | cons b t ih =>
    refine .head _ (t' := (⟨some (.inl ()),
      ⟨(StackTape.mapSome t).head, StackTape.cons (some b) L, (StackTape.mapSome t).tail⟩⟩ :
        (snocComputer c).Cfg)) _ _ ?_ ?_
    · rfl
    · simpa using ih (StackTape.cons (some b) L)

/-- Leftward pass then turn-around: from head over the first of `m` (left stack becomes the
right output), reach the halting configuration reading the reconstructed output, in
`m.length + 1` steps. -/
private lemma snocComputer_phaseB (c : Bool) : ∀ (m : List Bool) (R : StackTape Bool),
    RelatesInSteps (snocComputer c).TransitionRelation
      ⟨some (.inr ()), ⟨(StackTape.mapSome m).head, (StackTape.mapSome m).tail, R⟩⟩
      ⟨none, ⟨(snocPush R m).head, ∅, (snocPush R m).tail⟩⟩ (m.length + 1) := by
  intro m
  induction m with
  | nil => intro R; exact .single rfl
  | cons b t ih =>
    intro R
    refine .head _ (t' := (⟨some (.inr ()),
      ⟨(StackTape.mapSome t).head, (StackTape.mapSome t).tail, StackTape.cons (some b) R⟩⟩ :
        (snocComputer c).Cfg)) _ _ ?_ ?_
    · rfl
    · simpa using ih (StackTape.cons (some b) R)

private lemma snocPush_empty (l : List Bool) :
    snocPush (∅ : StackTape Bool) l = StackTape.mapSome l.reverse := by
  apply stackTape_ext
  rw [snocPush_toList]
  simp [StackTape.mapSome]

private lemma snocPush_final (c : Bool) (l : List Bool) :
    snocPush (StackTape.cons (some c) ∅) l.reverse = StackTape.mapSome (l ++ [c]) := by
  apply stackTape_ext
  rw [snocPush_toList, StackTape.cons_some_toList]
  simp [StackTape.mapSome]

/-- The append-a-bit machine outputs `l ++ [c]` within `2 * |l| + 2` steps. -/
lemma snocComputer_outputsWithinTime (c : Bool) (l : List Bool) :
    (snocComputer c).OutputsWithinTime l (l ++ [c]) (2 * l.length + 2) := by
  have hA := snocComputer_phaseA c ∅ l
  have hB := snocComputer_phaseB c l.reverse (StackTape.cons (some c) ∅)
  rw [← snocPush_empty l, snocPush_final c l] at hB
  have hchain :
      RelatesInSteps (snocComputer c).TransitionRelation
        ⟨some (.inl ()), (BiTape.mk₁ l : BiTape Bool)⟩
        ⟨none, (BiTape.mk₁ (l ++ [c]) : BiTape Bool)⟩
        (l.length + (1 + (l.reverse.length + 1))) := by
    rw [mk₁_eq l, mk₁_eq (l ++ [c])]
    exact hA.trans ((RelatesInSteps.single (by rfl)).trans hB)
  refine RelatesWithinSteps.of_le
    (RelatesWithinSteps.of_relatesInSteps hchain) ?_
  simp only [List.length_reverse]
  omega

/-- The append-a-bit machine is a `TimeComputable` witness for `fun l => l ++ [c]`. -/
def snocTimeComputable (c : Bool) : TimeComputable (fun l => l ++ [c]) where
  tm := snocComputer c
  timeBound n := 2 * n + 2
  outputsFunInTime l := snocComputer_outputsWithinTime c l

/-- The append-a-bit machine is a `PolyTimeComputable` witness for `fun l => l ++ [c]`. -/
noncomputable def snocPolyTimeComputable (c : Bool) :
    PolyTimeComputable (fun l => l ++ [c]) where
  toTimeComputable := snocTimeComputable c
  poly := 2 * Polynomial.X + Polynomial.C 2
  bounds n := by simp [snocTimeComputable, two_mul]

/-- The append-a-bit machine has two states. -/
theorem size_snocPolyTimeComputable (c : Bool) :
    (snocPolyTimeComputable c).size ≤ 2 := by
  change Fintype.card (Unit ⊕ Unit) ≤ 2
  simp

end Turing.SingleTapeTM

/-! ## Local support: appending a fixed bit, and finite iteration, at the encoding level -/

namespace Computability.EncPolyTime

open Turing.SingleTapeTM

/-- Append a fixed bit `c` to any encoding: the identity `σ → σ` viewed from encoding `es`
into the encoding `fun s => es s ++ [c]`, computed by the append-a-bit machine. -/
noncomputable def appendBit {σ : Type} (es : σ → List Bool) (c : Bool) :
    EncPolyTime es (fun s => es s ++ [c]) _root_.id where
  toFun l := l ++ [c]
  polyTime := snocPolyTimeComputable c
  map_encode _ := rfl

theorem size_appendBit {σ : Type} (es : σ → List Bool) (c : Bool) :
    (appendBit es c).size ≤ 2 := size_snocPolyTimeComputable c

/-- Finite iteration of a self-map witness: the `k`-fold composition is polynomial-time
computable, with description size at most `1 + k *` the single-step size. Composition adds
state counts (`size_comp`), so the bound is by induction on `k`. -/
theorem exists_iterate {σ : Type} (es : σ → List Bool) {g : σ → σ}
    (hstep : EncPolyTime es es g) :
    ∀ k : ℕ, ∃ h : EncPolyTime es es (g^[k]), h.size ≤ 1 + k * hstep.size := by
  intro k
  induction k with
  | zero =>
    refine ⟨(EncPolyTime.id es).copy (g^[0]) (fun s => ?_), ?_⟩
    · simp
    · simp
  | succ k ih =>
    obtain ⟨h, hh⟩ := ih
    refine ⟨(h.comp hstep).copy (g^[k+1]) (fun s => ?_), ?_⟩
    · exact (Function.iterate_succ_apply' g k s).symm
    · rw [size_copy, size_comp]
      have hmul : (k + 1) * hstep.size = k * hstep.size + hstep.size := by ring
      omega

end Computability.EncPolyTime

namespace OracleComp

/-! ## The realizable-predicate bridge

An implementing adversary's computed predicate `f n` at parameter `n` lands in
`Computability.RealizableLE n (d n)` for a polynomial description bound `d`, so a
predicate chosen to escape every polynomial realizable set (the diagonal of
`MachineCounting`) is implemented by no polynomial adversary. The `steps = 0` case is a
real proof (`realizable_of_implements_steps_eq_zero`): the initial-state readout factors
through only the initialization and output witnesses. The general case needs the compiled
run's factorization through the witness string functions, isolated as
`exists_poly_realizable_of_implements`. -/

/-- **[B-factor — the compiled deterministic run]** For an adversary implementing `pure ∘ f`
at the coin boundary, the input→output behavior `x ↦ (M n).output (run …)` at parameter `n`
is realized by an `EncPolyTime` initialization/output pair whose description sizes are
bounded by a single polynomial `q` in the adversary's `descBound` and `steps`.

Proof. Specialize `(himpl n).runK_eq` to `m := Id` and the deterministic constant-`true`
coin handler; the pure simulation collapses to `runD hdl (steps.eval n) (init x) = f n x`,
and `runD_eq_output_stateAfter` (using the adversary's `stable` readout to absorb early
termination) turns this into a readout of the fixed-fuel iterate of the one-step state map
`g = advanceOnce hdl M.toDynSystem`. That one-step map is compiled at the encoding level as
`updateF` precomposed with the fixed canonical coin answer `[true]` (built by the local
`Computability.EncPolyTime.appendBit` / `Turing.SingleTapeTM.snocComputer` support), and its
`steps.eval n`-fold composition is assembled by `Computability.EncPolyTime.exists_iterate`.
Composition adds machine-state counts, so the compiled initialization
`initF ▸ g^[steps.eval n]` has description size at most
`descBound + 1 + steps * (2 + descBound)` evaluated at `n` — one uniform polynomial `q`,
with the (parameter-specific) iteration time absorbed into `RealizableLE`'s time component.
This is the general-`steps` input to the diagonal contradiction; the `steps = 0` special
case is proved directly by `realizable_of_implements_steps_eq_zero`. -/
theorem exists_poly_realizable_of_implements
    (A : MachineAdversary (BoundaryData.coin BitEncFam.bitVecX BitEncFam.bool))
    (f : (n : ℕ) → BitVec n → Bool)
    (himpl : A.Implements (fun n x => (pure (f n x) : OracleComp coinSpec Bool))) :
    ∃ q : Polynomial ℕ, ∀ n, f n ∈ RealizableLE n (q.eval n) := by
  classical
  -- The deterministic constant-`true` coin handler.
  set hdl : OracleHandler coinSpec := OracleHandler.ofFn (fun _ => true) with hhdl
  refine ⟨A.descBound + Polynomial.C 1 + A.steps * (Polynomial.C 2 + A.descBound), fun n => ?_⟩
  set M := A.M n with hM
  set es := A.state.enc n with hes
  set k := A.steps.eval n with hk
  -- The one-step state map: expose the coin query, answer `true`, update.
  set g : M.State → M.State := OracleStrategy.advanceOnce hdl M.toDynSystem with hg
  -- `g` is the flattened update against the canonical `true` answer.
  have hg_upd : ∀ s, g s = M.updateFlat (s, ⟨M.expose s, true⟩) := by
    intro s
    rw [M.updateFlat_expose, hg, hhdl, OracleStrategy.advanceOnce, OracleHandler.ofFn_apply,
      PFunctor.PointedMachine.update_toDynSystem]
  -- The canonical coin answer encodes to the single bit `[true]`.
  have hin : ∀ s : M.State, es s ++ [true]
      = (A.state.pairVar (BoundaryData.coin BitEncFam.bitVecX BitEncFam.bool).eIface.encAns).enc n
          (s, ⟨M.expose s, true⟩) := by
    intro s
    rw [StrEncFam.pairVar_enc, hes]
    rfl
  have hout : ∀ s : M.State,
      es (g s) = A.state.enc n (M.updateFlat (s, ⟨M.expose s, true⟩)) := by
    intro s; rw [hes]; exact congrArg (A.state.enc n) (hg_upd s)
  -- The one-step witness: append the fixed answer, then run the update witness.
  set recoded : EncPolyTime (fun s => es s ++ [true]) es g :=
    (A.updateF.wit n).recode (fun s => (s, ⟨M.expose s, true⟩)) g hin hout with hrec
  set hstep : EncPolyTime es es g :=
    ((EncPolyTime.appendBit es true).comp recoded).copy g (fun _ => rfl) with hstepdef
  have hstep_size : hstep.size ≤ 2 + (A.updateF.wit n).size := by
    rw [hstepdef, EncPolyTime.size_copy, EncPolyTime.size_comp, hrec, EncPolyTime.size_recode]
    have := EncPolyTime.size_appendBit es true
    omega
  -- Finite iteration of the one-step map, `k = steps.eval n` times.
  obtain ⟨hIter, hIter_size⟩ := EncPolyTime.exists_iterate es hstep k
  -- Correctness: the compiled run reads out `f n x`.
  have hcorrect : ∀ x, M.output ((g^[k] ∘ M.init) x) = some (f n x) := by
    intro x
    have hstateAfter : g^[k] (M.init x)
        = OracleStrategy.stateAfter hdl M.toDynSystem (M.init x) k := by
      rw [hg]; rfl
    rw [Function.comp_apply, hstateAfter,
      ← M.runD_eq_output_stateAfter (A.stable n) hdl k (M.init x)]
    have key := (himpl n).runK_eq (m := Id) hdl.toQueryImpl x
    rw [OracleMachine.runD, hk, key]
    simp only [simulateQ_pure, map_pure]
    rfl
  -- Description-size bookkeeping.
  have hdesc : A.descBound.eval n = A.initF.size.eval n + A.exposeF.size.eval n
      + A.updateF.size.eval n + A.outputF.size.eval n := by
    simp [MachineAdversary.descBound]
  have hinit_le : (A.initF.wit n).size ≤ A.descBound.eval n :=
    (A.initF.size_le n).trans (by omega)
  have hupd_le : (A.updateF.wit n).size ≤ A.descBound.eval n :=
    (A.updateF.size_le n).trans (by omega)
  have hout_le : (A.outputF.wit n).size ≤ A.descBound.eval n :=
    (A.outputF.size_le n).trans (by omega)
  have hqeval : (A.descBound + Polynomial.C 1
      + A.steps * (Polynomial.C 2 + A.descBound)).eval n
      = A.descBound.eval n + 1 + k * (2 + A.descBound.eval n) := by
    rw [hk]; simp [Polynomial.eval_add, Polynomial.eval_mul]
  have hmul : k * hstep.size ≤ k * (2 + A.descBound.eval n) :=
    Nat.mul_le_mul_left k (hstep_size.trans (by omega))
  have hcomp_size : ((A.initF.wit n).comp hIter).size
      ≤ A.descBound.eval n + 1 + k * (2 + A.descBound.eval n) := by
    rw [EncPolyTime.size_comp]
    have := hIter_size
    omega
  refine ⟨M.State, es, g^[k] ∘ M.init, M.output, (A.initF.wit n).comp hIter,
    A.outputF.wit n, ?_, ?_, hcorrect⟩
  · -- initialization size
    rw [hqeval]
    exact hcomp_size
  · -- output size
    rw [hqeval]
    exact hout_le.trans (by omega)

/-- **Milestone A, realizability step (real).** A round-free adversary implementing
`pure ∘ f` realizes `f n` within its description bound: at `steps = 0` the run is the plain
readout of the initial state (`runK_zero`), so `(M n).output ((M n).init x) = some (f n x)`,
and the initialization and output witness families supply the required `EncPolyTime` pair
with sizes bounded by `descBound`. -/
private theorem realizable_of_implements_steps_eq_zero
    (A : MachineAdversary (BoundaryData.coin BitEncFam.bitVecX BitEncFam.bool))
    (f : (n : ℕ) → BitVec n → Bool)
    (himpl : A.Implements (fun n x => (pure (f n x) : OracleComp coinSpec Bool)))
    (hsteps : A.steps = 0) (n : ℕ) :
    f n ∈ RealizableLE n (A.descBound.eval n) := by
  have hout : ∀ x, (A.M n).output ((A.M n).init x) = some (f n x) := by
    intro x
    have h := himpl n
    rw [hsteps] at h
    simp only [Polynomial.eval_zero] at h
    have key := h.runK_eq (m := Id) (OracleHandler.ofFn (fun _ => true)).toQueryImpl x
    rw [OracleMachine.runK_zero] at key
    simp only [simulateQ_pure] at key
    exact key
  refine ⟨(A.M n).State, A.state.enc n, (A.M n).init, (A.M n).output,
    A.initF.wit n, A.outputF.wit n, ?_, ?_, hout⟩
  · exact (A.initF.size_le n).trans (by
      simp only [MachineAdversary.descBound, Polynomial.eval_add]; omega)
  · exact (A.outputF.size_le n).trans (by
      simp only [MachineAdversary.descBound, Polynomial.eval_add]; omega)

/-- **The diagonal predicate (real).** A predicate family `f` together with the covering
`Finset` family `S` of the threshold realizable sets, such that `f` escapes `S` cofinitely.
Assembled from the machine count (`exists_realizableLE_covering`), the count-versus-function
bound (`eventually_count_lt`), and the diagonal argument (`exists_diagonal`). -/
private theorem exists_diagonal_realizable :
    ∃ (f : (n : ℕ) → BitVec n → Bool) (S : (n : ℕ) → Finset (BitVec n → Bool)),
      (∀ n, RealizableLE n (2 ^ (n / 4)) ⊆ ↑(S n)) ∧
        (∀ᶠ n in Filter.atTop, f n ∉ S n) := by
  classical
  set S : (n : ℕ) → Finset (BitVec n → Bool) :=
    fun n => (exists_realizableLE_covering n (2 ^ (n / 4))).choose with hS
  have hcov : ∀ n, RealizableLE n (2 ^ (n / 4)) ⊆ ↑(S n) := fun n =>
    (exists_realizableLE_covering n (2 ^ (n / 4))).choose_spec.1
  have hcard : ∀ n, (S n).card ≤ Turing.SingleTapeTM.B (2 ^ (n / 4)) ^ 2 := fun n =>
    (exists_realizableLE_covering n (2 ^ (n / 4))).choose_spec.2
  have hSlt : ∀ᶠ n in Filter.atTop, (S n).card < 2 ^ (2 ^ n) :=
    eventually_count_lt.mono fun n h => lt_of_le_of_lt (hcard n) h
  obtain ⟨f, hf⟩ := exists_diagonal S hSlt
  exact ⟨f, S, hcov, hf⟩

/-- **The counting contradiction (real).** A diagonal predicate `f` escaping the threshold
realizable sets cofinitely is realized at no polynomial description bound: if `f n` were
realizable within `q.eval n` for every `n`, then cofinitely `q.eval n ≤ 2 ^ (n / 4)`
(`eventually_poly_le`), so `f n` would lie in the covered threshold set — contradicting that
it escapes it. -/
private theorem not_realizable_of_diagonal
    {f : (n : ℕ) → BitVec n → Bool} {S : (n : ℕ) → Finset (BitVec n → Bool)}
    (hcov : ∀ n, RealizableLE n (2 ^ (n / 4)) ⊆ ↑(S n))
    (hnot : ∀ᶠ n in Filter.atTop, f n ∉ S n) (q : Polynomial ℕ)
    (hreal : ∀ n, f n ∈ RealizableLE n (q.eval n)) : False := by
  have hmem : ∀ᶠ n in Filter.atTop, f n ∈ S n :=
    (eventually_poly_le q).mono fun n h =>
      Finset.mem_coe.mp (hcov n (realizableLE_mono h (hreal n)))
  obtain ⟨n, hin, hnotn⟩ := (hmem.and hnot).exists
  exact hnotn hin

/-! ## The certificates -/

/-- **Milestone A (sentinel)**: no family of *round-free* machine adversaries computes
every bitvector predicate. The `steps = 0` case needs no run analysis — the readout of
the initial state factors through just two witness machines — so it isolates the
counting core of the full certificate. False before boundary canonicalization (the
encoding-caching bundle above had `steps = 0`); its provability certifies the pinned
model. -/
theorem exists_not_implements_pure_of_steps_eq_zero :
    ∃ f : (n : ℕ) → BitVec n → Bool,
      ∀ A : MachineAdversary
          (BoundaryData.coin BitEncFam.bitVecX BitEncFam.bool),
        A.steps = 0 →
          ¬ A.Implements (fun n x => (pure (f n x) : OracleComp coinSpec Bool)) := by
  obtain ⟨f, S, hcov, hnot⟩ := exists_diagonal_realizable
  exact ⟨f, fun A hsteps himpl => not_realizable_of_diagonal hcov hnot A.descBound
    (realizable_of_implements_steps_eq_zero A f himpl hsteps)⟩

/-- **Milestone B (the acceptance target)**: the polynomial-time class at canonical
boundaries does not contain every bitvector predicate. This is the model's
non-triviality certificate — the statement whose provability separates a sound
definition of P/poly from the encoding-caching collapse, by counting: polynomially
many description bits per parameter cannot name doubly-exponentially many functions. -/
theorem exists_not_isPolyTime_pure :
    ∃ f : (n : ℕ) → BitVec n → Bool,
      ¬ OracleComp.IsPolyTime (BoundaryData.coin BitEncFam.bitVecX BitEncFam.bool)
          (fun n x => (pure (f n x) : OracleComp coinSpec Bool)) := by
  obtain ⟨f, S, hcov, hnot⟩ := exists_diagonal_realizable
  refine ⟨f, fun h => ?_⟩
  obtain ⟨w⟩ := h
  obtain ⟨q, hreal⟩ := exists_poly_realizable_of_implements w.A f w.implements
  exact not_realizable_of_diagonal hcov hnot q hreal

end OracleComp
