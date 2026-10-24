/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.SecretGuessCharge
public import HashSig.SLHDSA.SHAKE128s.Proof.GrowthCharge
public import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# Querying a node whose child's cell is unavailable

The input half of the budget is one event, not two. A canonical input is
`PK.seed ‖ ADRS ‖ (its children's cells)`, so a query at a node one of whose children's cells
the run cannot yet compute is a guess at that cell — and it is the same event whether the cell
is `SK.seed` at a `PRF` node, a WOTS chain value one step below the revealed digit, or an
unsigned FORS secret. Call such a node **sensitive**. This file charges the event at one unit
of `2 ^ -128` per query, with no multiple of it and no factor for the number of cells.

Three things give that rate, and they are the three fields of `Stakes`.

* **One cell at stake.** A sensitive node has exactly one unavailable child, so its canonical
  input is a function of a *single* cell: `inputOf node cell`. With two unavailable children
  the shape would take two cells and the statement below would not typecheck — which is where
  that hypothesis is spent. (Two would only make the event rarer; one is what makes a single
  coordinate the thing at stake.)
* **The address determines the node.** A canonical input carries its address in the clear, so
  `locate` reads the node off a candidate input before any cell is consulted. Hence a candidate
  can be the input of at most one node, and the union is over queries rather than over nodes.
* **The cell is one coordinate of a uniform table.** `stake` names it, and `coordinate_uniform`
  says a single coordinate of a uniform table of cells is a uniform cell.

A fourth condition is needed and is not probabilistic: availability must be **closed under
the structure**, a node all of whose children are available having an available cell. Without
it the charge is false outright — `Closed` and the section around it give the node shape that
breaks it, and `not_unavailable_of_obtainable` is what the condition buys.

Availability is a predicate on the run's own state — in the experiment, the signing log — and
is read at the state the query was made in, not at the end of the run. The set of unavailable
cells shrinks as signatures are issued, and a cell released mid-run may be queried freely
afterwards, so a region fixed before the run would charge events the run reaches honestly.

`prob_sensitive_le` is the per-candidate rate: a candidate input is sensitive at a state with
probability at most `2 ^ -128` over a uniform table, so a table drawn after the run costs one
unit of `2 ^ -128` per candidate it issued.
-/

public section

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.SensitiveQuery

/-- The value a graph cell carries: the bits a hash answer is truncated to. -/
abbrev Cell := Digest

/-- What the charge needs about the graph, and nothing else.

`inputOf node cell` is the canonical input of `node` when its single unavailable child's cell
takes the value `cell`; `locate` reads the node back off the address the input carries in the
clear; `stake` names the cell that child contributes. -/
structure Stakes (Node Index : Type) where
  /-- The canonical input of a node, as a function of the one cell at stake. -/
  inputOf : Node → Cell → Bytes
  /-- The node a candidate input's address names, if any. -/
  locate : Bytes → Option Node
  /-- The cell a node's unavailable child contributes. -/
  stake : Node → Index
  /-- The address is carried in the clear, so it recovers the node. -/
  locate_inputOf : ∀ node cell, locate (inputOf node cell) = some node
  /-- The payload carries the cell in the clear, so the input determines it. -/
  inputOf_injective : ∀ node, Function.Injective (inputOf node)

variable {Node Index State : Type}

/-- A candidate input is **sensitive** at a state when it is the canonical input of a node
whose staked cell is unavailable there, that cell taking the value the table gives it. -/
@[expose] def Sensitive (stakes : Stakes Node Index) (unavailable : State → Index → Prop)
    (table : Index → Cell) (state : State) (candidate : Bytes) : Prop :=
  ∃ node : Node, unavailable state (stakes.stake node) ∧
    stakes.inputOf node (table (stakes.stake node)) = candidate

/-! ## Availability has to be closed under the structure

The charge is false without one more condition, and it is not about probability. Suppose a
node `c` is *not* sensitive — every cell its canonical input mentions is available — but its
own cell is unavailable. A run may then query `c` legitimately, read `c`'s cell off the
answer, and from then on form the canonical input of the node above `c`, whose unavailable
child is exactly that cell. That node is sensitive for the whole run, and the run queries it
whenever it likes: the probability is one, not `2 ^ -128`, and no bound of the form
`queries / 2 ^ 128` can hold.

So availability must be closed under the structure: a node all of whose children are available
has an available cell. That is the force of counting as available "anything the public
structure derives from the disclosed cells". Under it, nothing unavailable is obtainable, which
is what makes a sensitive query the *first* place a run can reach an unavailable cell. -/

/-- The structure the closure condition speaks about: the cell a node's answer determines, and
the cells its canonical input mentions. -/
structure Graph (Node Index : Type) where
  /-- The cell a node's answer determines. -/
  cellOf : Node → Index
  /-- The cells a node's canonical input mentions. -/
  children : Node → Index → Prop

/-- **Availability is closed under the structure.** A node all of whose children's cells are
available has an available cell. -/
@[expose] def Closed (graph : Graph Node Index) (unavailable : State → Index → Prop) : Prop :=
  ∀ (state : State) (node : Node),
    (∀ index, graph.children node index → ¬ unavailable state index) →
      ¬ unavailable state (graph.cellOf node)

/-- The cells a run can compute from those it holds: a node's own cell once every cell its
canonical input mentions is in hand. -/
inductive Obtainable (graph : Graph Node Index) (known : Index → Prop) : Index → Prop
  | base {index : Index} (hknown : known index) : Obtainable graph known index
  | step {node : Node}
      (hchildren : ∀ index, graph.children node index → Obtainable graph known index) :
      Obtainable graph known (graph.cellOf node)

/-- **Nothing unavailable is obtainable.** Under closure, the cells a run can compute from the
available ones are themselves available, so the only way to an unavailable cell is a sensitive
query. -/
theorem not_unavailable_of_obtainable (graph : Graph Node Index)
    (unavailable : State → Index → Prop) (hclosed : Closed graph unavailable) (state : State)
    {index : Index}
    (hobtain : Obtainable graph (fun other => ¬ unavailable state other) index) :
    ¬ unavailable state index := by
  induction hobtain with
  | base hknown => exact hknown
  | step _ ih => exact hclosed state _ ih

/-! ## One coordinate of a uniform table

The whole rate is this: a candidate input names one node, the node names one cell, and that
cell is one coordinate of the uniform table. -/

variable [Fintype Index] [DecidableEq Index]

/-- A single coordinate of a uniform table of cells is a uniform cell. -/
theorem coordinate_uniform (index : Index) :
    ((fun table : Index → Cell => table index) <$>
        ($ᵗ (Index → Cell) : ProbComp (Index → Cell))) =ᵈ
      ($ᵗ Cell : ProbComp Cell) := by
  classical
  let split : (Index → Cell) ≃ Cell × ({other // other ≠ index} → Cell) :=
    Equiv.funSplitAt index Cell
  refine EvalDistEq.of_forall_prEvent_eq fun p => ?_
  rw [prEvent_map]
  calc Pr{let table ← ($ᵗ (Index → Cell) : ProbComp (Index → Cell))}[p (table index)]
      = Pr{let table ← ($ᵗ (Index → Cell) : ProbComp (Index → Cell))}[p (split table).1] := rfl
    _ = Pr{let z ← ($ᵗ (Cell × ({other // other ≠ index} → Cell)) :
          ProbComp (Cell × ({other // other ≠ index} → Cell)))}[p z.1] :=
        SampleableType.prEvent_uniformSample_equiv split (fun z => p z.1)
    _ = _ := SampleableType.prEvent_uniformSample_fst p

/-- A fixed coordinate of a uniform table takes a fixed value with probability `2 ^ -128`. -/
theorem prob_coordinate_eq (index : Index) (value : Cell) :
    Pr{let table ← ($ᵗ (Index → Cell) : ProbComp (Index → Cell))}[table index = value] =
      1 / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  classical
  calc Pr{let table ← ($ᵗ (Index → Cell) : ProbComp (Index → Cell))}[table index = value]
      = Pr{let cell ← (fun table : Index → Cell => table index) <$>
          ($ᵗ (Index → Cell) : ProbComp (Index → Cell))}[cell = value] := by
        rw [prEvent_map]
    _ = Pr{let cell ← ($ᵗ Cell : ProbComp Cell)}[cell = value] :=
        (coordinate_uniform index).prEvent_eq _
    _ = Pr{let cell ← ($ᵗ Cell : ProbComp Cell)}[value = cell] := by
        simp only [eq_comm]
    _ = _ := SecretGuessCharge.prob_single_guess value

/-! ## The per-candidate rate -/

/-- **A candidate input is sensitive with probability at most `2 ^ -128`.** The address names
the node before any cell is read, and the node names the one cell at stake, so a candidate is
a guess at a single coordinate of the table. -/
theorem prob_sensitive_le (stakes : Stakes Node Index)
    (unavailable : State → Index → Prop) (state : State) (candidate : Bytes) :
    Pr{let table ← ($ᵗ (Index → Cell) : ProbComp (Index → Cell))}[
        Sensitive stakes unavailable table state candidate] ≤
      1 / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  classical
  cases hlocate : stakes.locate candidate with
  | none =>
    -- No address, so no node: the event is empty.
    refine le_of_eq_of_le (b := 0)
      (prEvent_eq_zero_of_forall_mem_support _ _ fun table _ hbad => ?_) (by simp)
    obtain ⟨node, -, hinput⟩ := hbad
    rw [← hinput, stakes.locate_inputOf] at hlocate
    simp at hlocate
  | some node =>
    -- The address names this node, and the input then determines its cell.
    by_cases hpreimage : ∃ cell : Cell, stakes.inputOf node cell = candidate
    · obtain ⟨value, hvalue⟩ := hpreimage
      refine le_of_le_of_eq (prEvent_mono _ _ (fun table : Index → Cell =>
        table (stakes.stake node) = value) ?_) (prob_coordinate_eq _ value)
      rintro table ⟨other, -, hinput⟩
      have hsame : other = node := by
        have hother : stakes.locate candidate = some other := by
          rw [← hinput, stakes.locate_inputOf]
        exact Option.some.inj (hother.symm.trans hlocate)
      subst hsame
      exact stakes.inputOf_injective other (hinput.trans hvalue.symm)
    · refine le_of_eq_of_le (b := 0)
        (prEvent_eq_zero_of_forall_mem_support _ _ fun table _ hbad => ?_) (by simp)
      obtain ⟨other, -, hinput⟩ := hbad
      have hother : stakes.locate candidate = some other := by
        rw [← hinput, stakes.locate_inputOf]
      have hsame : other = node := Option.some.inj (hother.symm.trans hlocate)
      subst hsame
      exact hpreimage ⟨table (stakes.stake other), hinput⟩

end SlhDsaSecurity.SensitiveQuery
