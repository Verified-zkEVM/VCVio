/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import VCVio.OracleComp.SimSemantics.StateT.EqDistTriple
public import VCVio.OracleComp.SimSemantics.StateT.PreservesInv

/-!
# Equal-distribution triples between simulated programs

`QueryImpl.EqDistTriple so r P oa ob Q` relates two programs `oa` and `ob` over an oracle
specification, each run under one stateful interpretation `so`. It is, by definition, the triple
`OracleComp.EqDistTriple r P (simulateQ so oa) (simulateQ so ob) Q` of their simulations, so the
rules that do not look inside a program (`mono`, `frame`, `symm`, `of_support`,
`evalDist_run_eq`) are restatements of those of `OracleComp.EqDistTriple`.

The rules that do look inside a program transport the rules of `OracleComp.EqDistTriple` through
the simulation: `bind` and `pure` through `simulateQ_bind` and `simulateQ_pure`, and `ofFnM`
through the naturality of `Vector.ofFnM` under `simulateQ' so`. When every step of `so` moves the
state along the preorder `r`, every program forms a triple with itself (`refl_of_step`).
-/

public section

open OracleComp OracleSpec

namespace QueryImpl

variable {ι : Type} {spec : OracleSpec ι} {σ α β : Type}

/-- The programs `oa` and `ob` over `spec`, each run under the stateful interpretation `so`, form
an equal-distribution triple: from every state satisfying `P` their simulations have equal
output-and-state measures, and every outcome of the simulation of `ob` moves the state along `r`
and satisfies `Q`. -/
@[expose] def EqDistTriple (so : QueryImpl spec (StateT σ ProbComp)) (r : σ → σ → Prop)
    (P : σ → Prop) (oa ob : OracleComp spec α) (Q : α → σ → Prop) : Prop :=
  OracleComp.EqDistTriple r P (simulateQ so oa) (simulateQ so ob) Q

namespace EqDistTriple

variable {so : QueryImpl spec (StateT σ ProbComp)} {r : σ → σ → Prop} {P P' : σ → Prop}
  {oa ob : OracleComp spec α} {Q Q' : α → σ → Prop}

/-- A triple whose precondition is strengthened and whose postcondition is weakened. -/
theorem mono (h : so.EqDistTriple r P oa ob Q) (hP : ∀ s, P' s → P s)
    (hQ : ∀ a s, Q a s → Q' a s) : so.EqDistTriple r P' oa ob Q' :=
  OracleComp.EqDistTriple.mono h hP hQ

/-- A fact about the state that `r` preserves holds after both programs when it holds before. -/
theorem frame (h : so.EqDistTriple r P oa ob Q) {F : σ → Prop}
    (hF : ∀ s s', r s s' → F s → F s') :
    so.EqDistTriple r (fun s ↦ P s ∧ F s) oa ob (fun a s ↦ Q a s ∧ F s) :=
  OracleComp.EqDistTriple.frame h hF

/-- The two programs of a triple may be exchanged: their simulations have equal measures, hence
equal supports, so the outcomes of the left-hand simulation also satisfy the support condition. -/
theorem symm (h : so.EqDistTriple r P oa ob Q) : so.EqDistTriple r P ob oa Q :=
  OracleComp.EqDistTriple.symm h

/-- A program forms a triple with itself when the outcomes of its simulation from every state
satisfying `P` move the state along `r` and satisfy `Q`. -/
theorem of_support (h : ∀ s, P s → ∀ z ∈ support ((simulateQ so oa).run s), r s z.2 ∧ Q z.1 z.2) :
    so.EqDistTriple r P oa oa Q :=
  OracleComp.EqDistTriple.of_support h

/-- The simulations of the two programs of a triple have equal measures from every state
satisfying its precondition. -/
theorem evalDist_run_eq (h : so.EqDistTriple r P oa ob Q) {s : σ} (hs : P s)
    [MeasurableSpace (α × σ)] : 𝒟[(simulateQ so oa).run s] = 𝒟[(simulateQ so ob).run s] :=
  OracleComp.EqDistTriple.evalDist_run_eq h hs

/-- The right-hand program of a triple may be replaced by one with the same simulation. -/
theorem of_simulateQ_eq_right {ob' : OracleComp spec α} (h : so.EqDistTriple r P oa ob Q)
    (e : simulateQ so ob = simulateQ so ob') : so.EqDistTriple r P oa ob' Q := by
  rw [QueryImpl.EqDistTriple, ← e]
  exact h

/-- Returning one value from both sides. -/
theorem pure [Std.Refl r] (a : α) (h : ∀ s, P s → Q a s) :
    so.EqDistTriple r P (Pure.pure a) (Pure.pure a) Q := by
  rw [QueryImpl.EqDistTriple, simulateQ_pure]
  exact OracleComp.EqDistTriple.pure a h

/-- Sequential composition: the continuations need to be related only from the states and
outputs the simulation of the first right-hand program reaches. -/
theorem bind [IsTrans σ r] {f g : α → OracleComp spec β} {S : β → σ → Prop}
    (h : so.EqDistTriple r P oa ob Q) (hfg : ∀ a, so.EqDistTriple r (Q a) (f a) (g a) S) :
    so.EqDistTriple r P (oa >>= f) (ob >>= g) S := by
  rw [QueryImpl.EqDistTriple, simulateQ_bind, simulateQ_bind]
  exact OracleComp.EqDistTriple.bind h hfg

/-- When every step of `so` moves the state along the preorder `r`, every program forms a triple
with itself. -/
theorem refl_of_step [IsPreorder σ r] (hso : ∀ t s, ∀ z ∈ support ((so t).run s), r s z.2)
    (oa : OracleComp spec α) : so.EqDistTriple r P oa oa fun _ _ ↦ True :=
  of_support fun s _ z hz ↦
    ⟨OracleComp.simulateQ_run_preservesInv so (r s)
      (fun t _ hs z hz ↦ _root_.trans hs (hso t _ z hz)) oa s (_root_.refl s) z hz, trivial⟩

/-- Componentwise triples give a triple for `Vector.ofFnM`: if each pair of components `f i`,
`g i` preserves `Inv` and leaves its output related to the state by `R i`, and `R i` survives
every step along `r`, then the two vectors agree in distribution from every state satisfying
`Inv`, which they preserve, and every entry of the right-hand vector is related by its `R i` to
the final state. -/
theorem ofFnM [IsPreorder σ r] {k : ℕ} (Inv : σ → Prop) (R : Fin k → α → σ → Prop)
    (hR : ∀ i a s s', r s s' → R i a s → R i a s') {f g : Fin k → OracleComp spec α}
    (h : ∀ i, so.EqDistTriple r Inv (f i) (g i) fun a s ↦ Inv s ∧ R i a s) :
    so.EqDistTriple r Inv (Vector.ofFnM f) (Vector.ofFnM g)
      fun v s ↦ Inv s ∧ ∀ i, R i v[i] s := by
  have e : ∀ f : Fin k → OracleComp spec α,
      simulateQ so (Vector.ofFnM f) = Vector.ofFnM fun i ↦ simulateQ so (f i) :=
    fun f ↦ Vector.ofFnM_natural (simulateQ' so) f _ fun _ ↦ rfl
  rw [QueryImpl.EqDistTriple, e, e]
  exact Vector.ofFnM_eqDistTriple Inv R hR h

end EqDistTriple

end QueryImpl
