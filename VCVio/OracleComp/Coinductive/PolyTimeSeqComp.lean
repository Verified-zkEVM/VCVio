/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.Coinductive.PolyTime
import VCVio.OracleComp.Coinductive.SeqComp
import ToMathlib.Computability.MachineCombinators

/-!
# Sequential Composition of Polynomial-Time Adversaries (`IsPolyTime.bind`)

`MachineAdversary.seqComp eMid D₁ D₂` runs two machine adversaries in sequence through
PolyFun's two-phase machine `M₁ ⨟ M₂` (`PFunctor.PointedMachine.seqComp`: state
`S₁ ⊕ S₂`, hand-off to phase two exactly when phase one's readout resolves), at pinned
canonical boundaries sharing the mid boundary: `D₁` at `bd.withOut eMid` and `D₂` at
`bd.withIn eMid` compose to an adversary at `bd`. `OracleComp.IsPolyTime.bind` is the
resulting closure of the polynomial-time predicate under monadic sequencing — the last
missing closure of the polynomial-time calculus. No finiteness is assumed anywhere on
the mid type family: only its *encoding* is polynomial-width.

The three ledgers:

* **Semantics**: proven — `OracleMachine.Implements.seqComp`
  (`VCVio.OracleComp.Coinductive.SeqComp`) composes the two implements equations at the
  summed round budget, with the per-phase resolution certificates extracted from the
  implements equations themselves.
* **Query ledger**: proven — `OracleComp.isTotalQueryBound_bind` adds the two
  syntactic budgets.
* **TM step witnesses**: ride on the declared base-machine frontier of
  `ToMathlib.Computability.MachineCombinators` (`Computability.EncPolyTimeFam.sumElim`
  / `keep` / `takeFix` / `dropFix`, tickets S1–S4); this file adds no sorries of its
  own. The hand-off step (compute phase one's optional readout, keep the state,
  dispatch on the tag) is one shared witness assembly (`handoffF`) consumed by both
  the composite's initialization and its phase-one update; every layout change is a
  string-equal pure recode, recorded as its own private lemma.

Scope note: the phase-one update commutation `OracleMachine.updateFlat_seqComp_inl` —
hence the adversary former and `IsPolyTime.bind`, per parameter
(`[∀ n, Subsingleton (ι n)]`) — assumes a subsingleton index type. The flattened
update's tag-match guard can disagree between the composite and phase one on a
mismatched tag at an already-resolved phase-one state (the guard returns the state
unchanged, which differs from hand-off after the equally unchanged update), and a
subsingleton index type makes the guard always-true. This covers `coinSpec`
(`ι = Unit`), the boundary of every current textbook adversary; a general-`ι` version
needs an index-equality-test machine and is out of scope here. The phase-two equation
`updateFlat_seqComp_inr` holds at every index type.
-/

universe u

open OracleSpec Computability PFunctor

namespace OracleMachine

/-! ## The machine former: hand-off equations for `seqComp` -/

section Machine

variable {ι : Type u} {spec : OracleSpec.{u, u} ι} {α mid β : Type u}

/-- Where `seqComp` sends a phase-one state: hand off to `M₂` exactly when `M₁`'s
readout has resolved, re-injecting into phase one otherwise. -/
def handoff (M₁ : OracleMachine spec α mid) (M₂ : OracleMachine spec mid β)
    (s₁ : M₁.State) : (M₁ ⨟ M₂).State :=
  (M₁.output s₁).elim (Sum.inl s₁) (fun y => Sum.inr (M₂.init y))

/-- The composite's initialization is phase one's initialization followed by the
hand-off dispatch. -/
theorem seqComp_init_eq_handoff (M₁ : OracleMachine spec α mid)
    (M₂ : OracleMachine spec mid β) (x : α) :
    (M₁ ⨟ M₂).init x = M₁.handoff M₂ (M₁.init x) := by
  simp only [PointedMachine.seqComp_init, handoff]
  cases M₁.output (M₁.init x) <;> rfl

/-- The composite's update on a phase-one state is phase one's update followed by the
hand-off dispatch. -/
theorem seqComp_update_inl_eq_handoff (M₁ : OracleMachine spec α mid)
    (M₂ : OracleMachine spec mid β) (s₁ : M₁.State) (r : spec.Range (M₁.expose s₁)) :
    (M₁ ⨟ M₂).update (Sum.inl s₁) r = M₁.handoff M₂ (M₁.update s₁ r) := by
  simp only [PointedMachine.seqComp_update_inl, handoff]
  cases M₁.output (M₁.update s₁ r) <;> rfl

/-- Sequential composition preserves output stability: phase one never reads out, and a
resolved phase-two readout persists by `M₂`'s stability. -/
theorem stableOutput_seqComp {M₁ : OracleMachine spec α mid}
    {M₂ : OracleMachine spec mid β} (h₂ : M₂.StableOutput) :
    StableOutput (M₁ ⨟ M₂) := by
  intro s b hb r
  cases s with
  | inl s₁ => exact absurd hb (by simp)
  | inr s₂ => exact h₂ hb r

end Machine

/-! ## The flattened update of a composite

The phase-two equation holds at every oracle index type: `seqComp` preserves phase
two's `expose` on the nose, so the tag-match guard of `OracleMachine.updateFlat`
decides identically on both sides. The phase-one equation needs `[Subsingleton ι]`: on
a mismatched tag the composite's flattened update returns an `inl` state unchanged,
while hand-off after phase one's (equally unchanged) flattened update re-dispatches on
the readout — the two sides differ exactly at an already-resolved phase-one state. A
subsingleton index type (e.g. `coinSpec`, `ι = Unit`) makes the guard always-true; a
general-`ι` version awaits an index-equality-test machine. An `n`-dependent query
domain (e.g. a keyed left–right encryption spec) fails per-`n` Subsingleton as well, so
CPA-style reductions must route through oracle simulation rather than `bind` — flagged
for Stage 5/6. -/

section UpdateFlat

variable {ι : Type} [DecidableEq ι] {spec : OracleSpec.{0, 0} ι} {α mid β : Type}

/-- The flattened update of a composite on a phase-two state is phase two's flattened
update under `Sum.inr` — at every oracle index type, since the composite preserves
phase two's `expose` on the nose. -/
theorem updateFlat_seqComp_inr {M₁ : OracleMachine spec α mid}
    {M₂ : OracleMachine spec mid β} (s₂ : M₂.State) (a : (t : ι) × spec.Range t) :
    updateFlat (M₁ ⨟ M₂) (Sum.inr s₂, a) = Sum.inr (M₂.updateFlat (s₂, a)) := by
  obtain ⟨t, r⟩ := a
  by_cases h : M₂.expose s₂ = t
  · subst h
    exact (updateFlat_expose (M₁ ⨟ M₂) (Sum.inr s₂) r).trans
      (congrArg Sum.inr (M₂.updateFlat_expose s₂ r)).symm
  · have hL : updateFlat (M₁ ⨟ M₂) (Sum.inr s₂, ⟨t, r⟩) = Sum.inr s₂ := dif_neg h
    have hR : M₂.updateFlat (s₂, ⟨t, r⟩) = s₂ := dif_neg h
    rw [hL, hR]

/-- The flattened update of a composite on a phase-one state is phase one's flattened
update followed by the hand-off dispatch — at subsingleton oracle index types, where
the tag-match guard is always true. This covers `coinSpec` (`ι = Unit`); the section
docstring records why the equation genuinely fails at general `ι`. -/
theorem updateFlat_seqComp_inl [Subsingleton ι] {M₁ : OracleMachine spec α mid}
    {M₂ : OracleMachine spec mid β} (s₁ : M₁.State) (a : (t : ι) × spec.Range t) :
    updateFlat (M₁ ⨟ M₂) (Sum.inl s₁, a) = M₁.handoff M₂ (M₁.updateFlat (s₁, a)) := by
  obtain ⟨t, r⟩ := a
  have h : M₁.expose s₁ = t := Subsingleton.elim (α := ι) _ _
  subst h
  exact (updateFlat_expose (M₁ ⨟ M₂) (Sum.inl s₁) r).trans
    ((seqComp_update_inl_eq_handoff M₁ M₂ s₁ r).trans
      (congrArg (M₁.handoff M₂) (M₁.updateFlat_expose s₁ r).symm))

end UpdateFlat

end OracleMachine

/-! ## The adversary former -/

variable {ι : ℕ → Type} [∀ n, DecidableEq (ι n)]

namespace MachineAdversary

variable {spec : (n : ℕ) → OracleSpec.{0, 0} (ι n)} {α γ β : ℕ → Type}
  {bd : BoundaryData spec α β}

/-- Dispatch an optional value paired with a companion into the tag-bit sum shape:
`none` to a left padded-unit pair, `some y` to a right payload pair. A pure
re-bracketing — the encodings are string-equal (`sum_enc_optionSplit`). -/
private def optionSplit {τ σ : Type} : Option τ × σ → (PUnit × σ) ⊕ (τ × σ)
  | (none, s) => Sum.inl (PUnit.unit, s)
  | (some y, s) => Sum.inr (y, s)

/-- Distribute a tagged two-phase state over a trailing answer block. A pure
re-bracketing — the encodings are string-equal (`pairVar_sum_enc_sumDistrib`). -/
private def sumDistrib {σ₁ σ₂ τ : Type} : (σ₁ ⊕ σ₂) × τ → (σ₁ × τ) ⊕ (σ₂ × τ)
  | (Sum.inl s, a) => Sum.inl (s, a)
  | (Sum.inr s, a) => Sum.inr (s, a)

/-- The optional-readout layout is literally the tag-bit sum of the padded-unit and
payload pairs — `tag :: (payload ++ state)` on both sides — so `optionSplit` costs no
machine content. -/
private theorem sum_enc_optionSplit {τ σ : ℕ → Type} (e : BitEncFam τ) (s : StrEncFam σ)
    (n : ℕ) (p : Option (τ n) × σ n) :
    (((BitEncFam.pad e.wid e.widBound e.wid_le).pairFix s).sum (e.pairFix s)).enc n
      (optionSplit p) = ((e.option).pairFix s).enc n p := by
  obtain ⟨o, x⟩ := p
  cases o <;> rfl

/-- Appending the answer block under a two-phase state tag re-brackets to the sum of
the per-phase state/answer pairs — `tag :: (state ++ answer)` on both sides — so
`sumDistrib` costs no machine content. -/
private theorem pairVar_sum_enc_sumDistrib {σ₁ σ₂ τ : ℕ → Type} (s₁ : StrEncFam σ₁)
    (s₂ : StrEncFam σ₂) (e : BitEncFam τ) (n : ℕ) (q : (σ₁ n ⊕ σ₂ n) × τ n) :
    ((s₁.sum s₂).pairVar e).enc n q =
      ((s₁.pairVar e).sum (s₂.pairVar e)).enc n (sumDistrib q) := by
  obtain ⟨x, a⟩ := q
  cases x <;> rfl

section SeqComp

variable (eMid : BitEncFam γ) (D₁ : MachineAdversary (bd.withOut eMid))
  (D₂ : MachineAdversary (bd.withIn eMid))

/-- Phase one's optional readout retained in front of its state and re-bracketed into
the tag-bit sum layout: the frontier's `keep` computes the readout block, and the
layout change is a pure recode along `sum_enc_optionSplit`. -/
private noncomputable def splitF :
    EncPolyTimeFam D₁.state.enc
      ((((BitEncFam.pad eMid.wid eMid.widBound eMid.wid_le).pairFix D₁.state).sum
        (eMid.pairFix D₁.state)).enc)
      (fun n s => optionSplit ((D₁.M n).output s, s)) :=
  (EncPolyTimeFam.keep D₁.state eMid.option D₁.outputF).recode (fun _ s => s)
    (fun n s => optionSplit ((D₁.M n).output s, s)) (fun _ _ => rfl)
    (fun n s => sum_enc_optionSplit eMid D₁.state n ((D₁.M n).output s, s))

/-- Tag dispatch of the split readout: an unresolved left branch drops the padding and
re-injects into phase one, a resolved right branch projects the readout and initializes
phase two. -/
private noncomputable def dispatchF :
    EncPolyTimeFam
      ((((BitEncFam.pad eMid.wid eMid.widBound eMid.wid_le).pairFix D₁.state).sum
        (eMid.pairFix D₁.state)).enc)
      ((D₁.state.sum D₂.state).enc)
      (fun n => Sum.elim (fun p => Sum.inl p.2)
        (fun p => Sum.inr ((D₂.M n).init p.1))) :=
  (EncPolyTimeFam.sumElim
    ((BitEncFam.pad eMid.wid eMid.widBound eMid.wid_le).pairFix D₁.state)
    (eMid.pairFix D₁.state)
    (EncPolyTimeFam.dropFix (BitEncFam.pad eMid.wid eMid.widBound eMid.wid_le) D₁.state
      (EncPolyTimeFam.inlWit D₁.state D₂.state))
    (((EncPolyTimeFam.takeFix eMid D₁.state).comp D₂.initF).comp
      (EncPolyTimeFam.inrWit D₁.state D₂.state))).copy
    (fun n => Sum.elim (fun p => Sum.inl p.2) (fun p => Sum.inr ((D₂.M n).init p.1)))
    (fun n s => by cases s <;> rfl)

/-- The shared hand-off witness: compute phase one's optional readout, keep the state,
and dispatch on the tag — `none` stays in phase one, `some y` initializes phase two.
Consumed by both the composite's initialization and its phase-one update. -/
private noncomputable def handoffF :
    EncPolyTimeFam D₁.state.enc ((D₁.state.sum D₂.state).enc)
      (fun n => (D₁.M n).handoff (D₂.M n)) :=
  ((splitF eMid D₁).comp (dispatchF eMid D₁ D₂)).copy
    (fun n => (D₁.M n).handoff (D₂.M n))
    (fun n s => by
      cases h : (D₁.M n).output s <;>
        simp [optionSplit, OracleMachine.handoff, h])

variable [∀ n, Subsingleton (ι n)]

/-- Pointwise action of the composite's flattened update in the distributed layout:
the phase-one branch steps and hands off (`OracleMachine.updateFlat_seqComp_inl`, at
subsingleton index types), the phase-two branch steps in place
(`OracleMachine.updateFlat_seqComp_inr`). -/
private theorem seqComp_updateFlat_elim (n : ℕ)
    (q : ((D₁.M n).State ⊕ (D₂.M n).State) × ((t : ι n) × (spec n).Range t)) :
    OracleMachine.updateFlat (D₁.M n ⨟ D₂.M n) q =
      Sum.elim (fun p => (D₁.M n).handoff (D₂.M n) ((D₁.M n).updateFlat p))
        (fun p => Sum.inr ((D₂.M n).updateFlat p)) (sumDistrib q) := by
  obtain ⟨x, a⟩ := q
  cases x with
  | inl s₁ => exact OracleMachine.updateFlat_seqComp_inl s₁ a
  | inr s₂ => exact OracleMachine.updateFlat_seqComp_inr s₂ a

/-- Sequential composition of machine adversaries at a shared mid boundary `eMid`:
PolyFun's two-phase machine `D₁.M n ⨟ D₂.M n` at the summed round budget, with state
representation the tag-bit sum of the phases' representations. The step witnesses:
initialization is `D₁`'s followed by the shared hand-off assembly (`handoffF`), query
selection and readout dispatch on the state tag (`sumElim`, with a constant-`none`
readout in phase one), and the flattened update dispatches to `D₁`'s update-then-hand-
off or `D₂`'s update under the tag, recoded along the string-equal `sumDistrib` layout.
Requires `[Subsingleton ι]` for the phase-one update commutation (see the module
docstring). -/
noncomputable def seqComp : MachineAdversary bd where
  M n := D₁.M n ⨟ D₂.M n
  steps := D₁.steps + D₂.steps
  stable n := OracleMachine.stableOutput_seqComp (D₂.stable n)
  state := D₁.state.sum D₂.state
  initF := (D₁.initF.comp (handoffF eMid D₁ D₂)).copy _
    (fun n x => (OracleMachine.seqComp_init_eq_handoff (D₁.M n) (D₂.M n) x).symm)
  exposeF := (EncPolyTimeFam.sumElim D₁.state D₂.state D₁.exposeF D₂.exposeF).copy _
    (fun n s => by cases s <;> rfl)
  updateF := (EncPolyTimeFam.sumElim (D₁.state.pairVar bd.eIface.encAns)
      (D₂.state.pairVar bd.eIface.encAns)
      (D₁.updateF.comp (handoffF eMid D₁ D₂))
      (D₂.updateF.comp (EncPolyTimeFam.inrWit D₁.state D₂.state))).recode
    (fun _ q => sumDistrib q)
    (fun n => OracleMachine.updateFlat (D₁.M n ⨟ D₂.M n))
    (pairVar_sum_enc_sumDistrib D₁.state D₂.state bd.eIface.encAns)
    (fun n q => congrArg ((D₁.state.sum D₂.state).enc n)
      (seqComp_updateFlat_elim eMid D₁ D₂ n q))
  outputF := (EncPolyTimeFam.sumElim D₁.state D₂.state
      (EncPolyTimeFam.const D₁.state.enc (fun n => (none : Option (β n)))
        (bd.eOut.option).widBound
        (fun n => ((bd.eOut.option).len_eq n none).le.trans ((bd.eOut.option).wid_le n)))
      D₂.outputF).copy _
    (fun n s => by cases s <;> rfl)

@[simp] theorem seqComp_M (n : ℕ) :
    (seqComp eMid D₁ D₂).M n = (D₁.M n ⨟ D₂.M n) := rfl

@[simp] theorem seqComp_steps :
    (seqComp eMid D₁ D₂).steps = D₁.steps + D₂.steps := rfl

end SeqComp

/-- The composite adversary implements the bound program family at the summed round
budget: per parameter this is the proven semantic composition law
`OracleMachine.Implements.seqComp`. -/
theorem seqComp_implements [∀ n, Subsingleton (ι n)] {eMid : BitEncFam γ}
    {D₁ : MachineAdversary (bd.withOut eMid)} {D₂ : MachineAdversary (bd.withIn eMid)}
    {oa : (n : ℕ) → α n → OracleComp (spec n) (γ n)}
    {ob : (n : ℕ) → γ n → OracleComp (spec n) (β n)}
    (h₁ : D₁ ⊨ oa) (h₂ : D₂ ⊨ ob) :
    D₁.seqComp eMid D₂ ⊨ fun n x => oa n x >>= ob n := by
  intro n
  have key := OracleMachine.Implements.seqComp (h₁ n) (h₂ n)
  simpa only [seqComp_M, seqComp_steps, Polynomial.eval_add] using key

end MachineAdversary

/-! ## The witness and predicate closures -/

/-- Sequential composition of polynomial-time certificates at a shared mid boundary:
the adversaries compose by `MachineAdversary.seqComp`, the implements proofs by the
semantic law, and the syntactic budgets by `OracleComp.isTotalQueryBound_bind`. -/
noncomputable def PolyTimeWitness.seqComp [∀ n, Subsingleton (ι n)]
    {spec : (n : ℕ) → OracleSpec.{0, 0} (ι n)} {α γ β : ℕ → Type}
    {bd : BoundaryData spec α β}
    {eMid : BitEncFam γ} {oa : (n : ℕ) → α n → OracleComp (spec n) (γ n)}
    {ob : (n : ℕ) → γ n → OracleComp (spec n) (β n)}
    (w₁ : PolyTimeWitness (bd.withOut eMid) oa)
    (w₂ : PolyTimeWitness (bd.withIn eMid) ob) :
    PolyTimeWitness bd (fun n x => oa n x >>= ob n) where
  A := w₁.A.seqComp eMid w₂.A
  implements := MachineAdversary.seqComp_implements w₁.implements w₂.implements
  queryBound := fun n x => by
    simp only [MachineAdversary.seqComp_steps, Polynomial.eval_add]
    exact OracleComp.isTotalQueryBound_bind (w₁.queryBound n x) fun y => w₂.queryBound n y

/-- **`OracleComp.IsPolyTime` is closed under monadic sequencing** at a shared pinned
mid boundary `eMid`: if `oa` is polynomial time into `eMid` and `ob` is polynomial time
out of it, then `fun n x => oa n x >>= ob n` is polynomial time — the last missing
closure of the polynomial-time calculus, over subsingleton oracle index types
(`coinSpec` in particular; see the module docstring). The mid type family may be
superpolynomially large: only its encoding is polynomial-width. -/
theorem OracleComp.IsPolyTime.bind [∀ n, Subsingleton (ι n)]
    {spec : (n : ℕ) → OracleSpec.{0, 0} (ι n)}
    {α γ β : ℕ → Type} {bd : BoundaryData spec α β} (eMid : BitEncFam γ)
    {oa : (n : ℕ) → α n → OracleComp (spec n) (γ n)}
    {ob : (n : ℕ) → γ n → OracleComp (spec n) (β n)}
    (h₁ : OracleComp.IsPolyTime (bd.withOut eMid) oa)
    (h₂ : OracleComp.IsPolyTime (bd.withIn eMid) ob) :
    OracleComp.IsPolyTime bd fun n x => oa n x >>= ob n := by
  obtain ⟨w₁⟩ := h₁
  obtain ⟨w₂⟩ := h₂
  exact ⟨w₁.seqComp w₂⟩
