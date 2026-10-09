/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import VCVio.OracleComp.ProbComp.Basic
public import VCVio.OracleComp.EvalDist.Measure
public import ToMathlib.Data.Vector
public import ToMathlib.Order.RelClasses

/-!
# Equal-distribution triples for stateful probabilistic programs

`OracleComp.EqDistTriple r P mx my Q` compares two programs in `StateT σ ProbComp`: from every
state satisfying the precondition `P`, they have equal output-and-state measures, and every
outcome of `my` moves the state along `r` and satisfies the postcondition `Q`. The relation `r`
is a preorder of state growth: a fact about the state that `r` preserves, such as a value being
recorded in a cache that only grows, carries from one program of a sequence to the later ones
(`OracleComp.EqDistTriple.frame`).

The postcondition is stated on the right-hand program. Programs with equal measures have equal
supports, so exchanging the two programs gives a triple with the same pre- and postcondition
(`OracleComp.EqDistTriple.symm`), and the postcondition holds of either side.

Triples compose by `OracleComp.EqDistTriple.bind`: the continuations need to agree only on the
outcomes of the first right-hand program, so two programs built by one monadic combinator from
callbacks related by triples are related by a triple. This file records the rules and the case
of `Vector.ofFnM`; the effectful Merkle traversals are treated in
`VCVio.CryptoFoundations.MerkleTree.Addressed.NatIndexed.EqDistTriple`. Along the trivial
preorder `⊤`, with `P` and `Q` trivial, a triple is equality of measures from every state
(`OracleComp.EqDistTriple.of_evalDist_run_eq`).

A triple is the diagonal-coupling case of `OracleComp.MeasureRelational.wp`: the two runs are
coupled on equal outcomes, with the postcondition on one side. It is stated as an equality of
measures under every measurable structure on the outcomes. Its support half generalises
`StateT.PreservesInv` with outputs, a growth relation and a postcondition:
`EqDistTriple ⊤ Inv mx mx fun _ ↦ Inv` holds exactly when `StateT.PreservesInv mx Inv` does.

A triple between the signing algorithms of two signature schemes, with precondition `I` and
postcondition `fun _ ↦ I`, gives the signing-stage hypotheses of
`SignatureAlg.evalDist_simulateQ_run_unforgeableTranscriptExperiment_congr_of_inv`: equality of
measures by `OracleComp.EqDistTriple.evalDist_run_eq`, and preservation of `I` by the signing
algorithm of the first scheme by the support condition with that scheme on the right, through
`OracleComp.EqDistTriple.symm` if needed.

For programs over an oracle specification run under one stateful interpretation `so`,
`QueryImpl.EqDistTriple so` is, by definition, the triple of their simulations under `so`
(`VCVio.OracleComp.SimSemantics.StateT.EqDistTriple.Simulate`).
-/

public section

open OracleSpec MeasureTheory

namespace OracleComp

variable {σ α β : Type}

/-- From every state satisfying `P`, the stateful programs `mx` and `my` have equal
output-and-state measures under every measurable structure, and every outcome `z` of `my` from
such a state `s` satisfies `r s z.2` and `Q z.1 z.2`. The postcondition is stated on the
right-hand program `my`; `OracleComp.EqDistTriple.symm` transfers it to the left-hand one. -/
@[expose] def EqDistTriple (r : σ → σ → Prop) (P : σ → Prop) (mx my : StateT σ ProbComp α)
    (Q : α → σ → Prop) : Prop :=
  ∀ s, P s → (∀ [MeasurableSpace (α × σ)], 𝒟[mx.run s] = 𝒟[my.run s]) ∧
    ∀ z ∈ support (my.run s), r s z.2 ∧ Q z.1 z.2

namespace EqDistTriple

variable {r : σ → σ → Prop} {P P' : σ → Prop} {mx my : StateT σ ProbComp α}
  {Q Q' : α → σ → Prop}

/-- A triple whose precondition is strengthened and whose postcondition is weakened. -/
theorem mono (h : EqDistTriple r P mx my Q) (hP : ∀ s, P' s → P s)
    (hQ : ∀ a s, Q a s → Q' a s) : EqDistTriple r P' mx my Q' := fun s hs ↦
  ⟨(h s (hP s hs)).1, fun z hz ↦ ((h s (hP s hs)).2 z hz).imp_right (hQ _ _)⟩

/-- A fact about the state that `r` preserves holds after both programs when it holds before. -/
theorem frame (h : EqDistTriple r P mx my Q) {F : σ → Prop} (hF : ∀ s s', r s s' → F s → F s') :
    EqDistTriple r (fun s ↦ P s ∧ F s) mx my (fun a s ↦ Q a s ∧ F s) := fun s hs ↦
  ⟨(h s hs.1).1, fun z hz ↦ have h' := (h s hs.1).2 z hz; ⟨h'.1, h'.2, hF _ _ h'.1 hs.2⟩⟩

/-- The two programs of a triple may be exchanged: equal measures give equal supports, so the
outcomes of the left-hand program also satisfy the support condition. -/
theorem symm (h : EqDistTriple r P mx my Q) : EqDistTriple r P my mx Q := fun s hs ↦
  ⟨fun {_} ↦ (h s hs).1.symm,
    fun z hz ↦ (h s hs).2 z ((support_eq_of_evalDist_eq (h s hs).1).subset hz)⟩

/-- A program forms a triple with itself when its outcomes from every state satisfying `P`
move the state along `r` and satisfy `Q`. -/
theorem of_support (h : ∀ s, P s → ∀ z ∈ support (mx.run s), r s z.2 ∧ Q z.1 z.2) :
    EqDistTriple r P mx mx Q := fun s hs ↦ ⟨rfl, h s hs⟩

/-- The two programs of a triple have equal measures from every state satisfying its
precondition. -/
theorem evalDist_run_eq (h : EqDistTriple r P mx my Q) {s : σ} (hs : P s)
    [MeasurableSpace (α × σ)] : 𝒟[mx.run s] = 𝒟[my.run s] :=
  (h s hs).1

/-- Programs with equal measures from every state satisfying `P` form a triple along the
trivial preorder, for any postcondition that always holds. -/
theorem of_evalDist_run_eq (h : ∀ s, P s → ∀ [MeasurableSpace (α × σ)], 𝒟[mx.run s] = 𝒟[my.run s])
    (hQ : ∀ a s, Q a s) : EqDistTriple ⊤ P mx my Q := fun s hs ↦
  ⟨h s hs, fun _ _ ↦ ⟨trivial, hQ _ _⟩⟩

/-- Returning one value from both sides. -/
theorem pure [Std.Refl r] (a : α) (h : ∀ s, P s → Q a s) :
    EqDistTriple r P (Pure.pure a) (Pure.pure a) Q := fun s hs ↦
  ⟨rfl, fun z hz ↦ by
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    exact hz ▸ ⟨refl s, h s hs⟩⟩

/-- Sequential composition: the continuations need to be related only from the states and
outputs the first right-hand program reaches. -/
theorem bind [IsTrans σ r] {f g : α → StateT σ ProbComp β} {S : β → σ → Prop}
    (h : EqDistTriple r P mx my Q) (hfg : ∀ a, EqDistTriple r (Q a) (f a) (g a) S) :
    EqDistTriple r P (mx >>= f) (my >>= g) S := by
  intro s hs
  obtain ⟨heq, hpost⟩ := h s hs
  refine ⟨fun {_} ↦ ?_, fun z hz ↦ ?_⟩
  · simp only [StateT.run_bind]
    exact (evalDist_bind_congr_left_of_forall heq _).trans <|
      evalDist_bind_congr_of_support _ _ _ fun w hw ↦ (hfg w.1 w.2 (hpost w hw).2).1
  · rw [StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨w, hw, hz⟩ := hz
    obtain ⟨hz₁, hz₂⟩ := (hfg w.1 w.2 (hpost w hw).2).2 z hz
    exact ⟨_root_.trans (hpost w hw).1 hz₁, hz₂⟩

end EqDistTriple

end OracleComp

namespace Vector

open OracleComp

variable {σ α : Type}

/-- Componentwise triples give a triple for `Vector.ofFnM`. If each pair of components `f i`,
`g i` preserves `Inv` and leaves its output related to the state by `R i`, and `R i` survives
every step along `r`, then the two vectors agree in distribution from every state satisfying
`Inv`, which they preserve, and every entry of the right-hand vector is related by its `R i` to
the final state. -/
theorem ofFnM_eqDistTriple {r : σ → σ → Prop} [IsPreorder σ r] {k : ℕ} (Inv : σ → Prop)
    (R : Fin k → α → σ → Prop) (hR : ∀ i a s s', r s s' → R i a s → R i a s')
    {f g : Fin k → StateT σ ProbComp α}
    (h : ∀ i, EqDistTriple r Inv (f i) (g i) fun a s ↦ Inv s ∧ R i a s) :
    EqDistTriple r Inv (ofFnM f) (ofFnM g)
      fun v s ↦ Inv s ∧ ∀ i, R i v[i] s := by
  induction k with
  | zero =>
    rw [ofFnM_zero, ofFnM_zero]
    exact EqDistTriple.pure _ fun s hs ↦ ⟨hs, fun i ↦ i.elim0⟩
  | succ k ih =>
    rw [ofFnM_succ, ofFnM_succ]
    refine (ih _ (fun i ↦ hR i.castSucc) fun i ↦ h i.castSucc).bind fun xs ↦ ?_
    refine ((h (Fin.last k)).frame (F := fun s ↦ ∀ i : Fin k, R i.castSucc xs[i] s)
      fun s s' hs hF i ↦ hR _ _ _ _ hs (hF i)).bind fun x ↦ EqDistTriple.pure _ fun s hs ↦
        ⟨hs.1.1, Fin.lastCases ?_ fun i ↦ ?_⟩
    · simpa using hs.1.2
    · simpa [getElem_push_lt] using hs.2 i

end Vector
