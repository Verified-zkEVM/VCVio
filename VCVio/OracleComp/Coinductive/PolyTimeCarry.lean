/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.Coinductive.PolyTime
import ToMathlib.Computability.MachineCombinators

/-!
# The Carry (Strength) Former for Polynomial-Time Adversaries

`OracleMachine.carry γ M` runs `M` while holding a value `c : γ` inert alongside its
state — the monoidal strength of the machine layer. `MachineAdversary.carry e D` is the
family-level former at pinned canonical boundaries: the carried component is a
fixed-width block `e : Computability.BitEncFam γ` prefixed to the input, state, and
output encodings, and `OracleComp.IsPolyTime.carry` is the resulting closure of the
polynomial-time predicate under `fun p => (p.1, ·) <$> oa p.2`.

This is the strength primitive of the reduction pipeline: a reduction's own input
(a PRG challenge `y`) must cross the constructed adversary's choose phase, and a
sampled challenge bit must cross its distinguish phase — both are fixed-width values
carried inert through an oracle-using computation.

The three ledgers:

* **Semantics**: proven — `OracleMachine.runK_carry` (the carried value factors out of
  the fuelled run, in every lawful monad), hence `OracleMachine.Implements.carry` and
  `MachineAdversary.carry_implements`.
* **Query ledger**: proven — the mapped program family keeps the round budget
  (`OracleComp.isQueryBound_map_iff` inside `OracleComp.IsPolyTime.carry`).
* **TM step witnesses**: ride on the declared base-machine frontier of
  `ToMathlib.Computability.MachineCombinators` (`Computability.EncPolyTimeFam.dropFix` /
  `underPrefix` / `optionUnder`, tickets S4–S6); this file adds no sorries of its own.

`OracleMachine.updateFlat_carry` — the commuting law for the flattened update —
requires no assumption on the oracle index type: `carry` preserves `expose` on the
nose, so the tag-match guard of `OracleMachine.updateFlat` agrees between the carried
and the underlying machine at every query index.
-/

universe u

open OracleSpec Computability

namespace OracleMachine

/-! ## The machine former -/

section Machine

variable {ι : Type u} {spec : OracleSpec.{u, u} ι} {α β : Type u}

/-- Run a machine while carrying a fixed value `c : γ` alongside: same interface, state
`γ × State`, the carried component inert. The machine-level monoidal strength — the
value crosses the whole oracle-using run untouched and is re-paired with the readout. -/
def carry (γ : Type u) (M : OracleMachine spec α β) :
    OracleMachine spec (γ × α) (γ × β) where
  State := γ × M.State
  expose s := M.expose s.2
  update s r := (s.1, M.update s.2 r)
  init x := (x.1, M.init x.2)
  output s := (M.output s.2).map (s.1, ·)

@[simp] theorem carry_expose (γ : Type u) (M : OracleMachine spec α β) (s : γ × M.State) :
    (M.carry γ).expose s = M.expose s.2 := rfl

@[simp] theorem carry_update (γ : Type u) (M : OracleMachine spec α β) (s : γ × M.State)
    (r : spec.Range (M.expose s.2)) : (M.carry γ).update s r = (s.1, M.update s.2 r) := rfl

@[simp] theorem carry_init (γ : Type u) (M : OracleMachine spec α β) (x : γ × α) :
    (M.carry γ).init x = (x.1, M.init x.2) := rfl

@[simp] theorem carry_output (γ : Type u) (M : OracleMachine spec α β) (s : γ × M.State) :
    (M.carry γ).output s = (M.output s.2).map (s.1, ·) := rfl

/-- Carrying preserves output stability: the carried component never changes, and the
underlying readout persists. -/
theorem stableOutput_carry {γ : Type u} {M : OracleMachine spec α β}
    (h : M.StableOutput) : (M.carry γ).StableOutput := by
  intro s c hc r
  simp only [carry_output] at hc ⊢
  obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp hc
  simp only [carry_update]
  exact Option.map_eq_some_iff.mpr ⟨b, h hb r, rfl⟩

/-- **The carried value factors out of the fuelled run**: running the carried machine
from `(c, s)` is running the underlying machine from `s` and re-pairing the optional
readout with `c` — in every lawful monad, at every fuel. -/
theorem runK_carry {m : Type u → Type u} [Monad m] [LawfulMonad m] (γ : Type u)
    (M : OracleMachine spec α β) (H : QueryImpl spec m) (k : ℕ) (c : γ) (s : M.State) :
    (M.carry γ).runK H k (c, s) = Option.map (c, ·) <$> M.runK H k s := by
  induction k generalizing s with
  | zero => simp only [runK_zero, carry_output, map_pure]
  | succ k ih =>
    cases hb : M.output s with
    | some b =>
      rw [(M.carry γ).runK_of_output_eq_some H
          (show (M.carry γ).output (c, s) = some (c, b) by simp [hb]) (k + 1),
        M.runK_of_output_eq_some H hb (k + 1), map_pure]
      simp
    | none =>
      rw [(M.carry γ).runK_succ_of_output_eq_none H
          (show (M.carry γ).output (c, s) = none by simp [hb]) k,
        M.runK_succ_of_output_eq_none H hb, map_bind]
      simp only [carry_expose, carry_update]
      exact bind_congr fun r => ih (M.update s r)

/-- An implementing machine's carry implements the strength-mapped program: pair the
carried component with every result of the underlying program family. -/
theorem Implements.carry {γ : Type u} {M : OracleMachine spec α β}
    {oa : α → OracleComp spec β} {k : ℕ} (h : M ⊨[k] oa) :
    M.carry γ ⊨[k] fun p : γ × α => (p.1, ·) <$> oa p.2 := by
  intro m _ _ H p
  rw [carry_init, runK_carry, h H p.2]
  simp [simulateQ_map, Functor.map_map]

end Machine

/-! ## The flattened update commutes with carrying

No index-equality assumption is needed: `carry` preserves `expose` on the nose, so the
tag-match guard of `updateFlat` decides identically for the carried and the underlying
machine, at every oracle index. -/

section UpdateFlat

variable {ι : Type} [DecidableEq ι] {spec : OracleSpec.{0, 0} ι} {α β : Type}

/-- The flattened update of a carried machine is the flattened update of the underlying
machine under the inert first component — the exact commuting equation consumed by the
Turing-machine witness of `MachineAdversary.carry`. Holds for every oracle index type
because `carry` preserves `expose`, so the dependent tag guard agrees on both sides. -/
theorem updateFlat_carry {γ : Type} {M : OracleMachine spec α β}
    (p : (γ × M.State) × ((t : ι) × spec.Range t)) :
    (M.carry γ).updateFlat p = (p.1.1, M.updateFlat (p.1.2, p.2)) := by
  obtain ⟨⟨c, s⟩, t, r⟩ := p
  change (M.carry γ).updateFlat ((c, s), ⟨t, r⟩) = (c, M.updateFlat (s, ⟨t, r⟩))
  by_cases h : M.expose s = t
  · subst h
    exact ((M.carry γ).updateFlat_expose (c, s) r).trans
      (congrArg (Prod.mk c) (M.updateFlat_expose s r)).symm
  · have hL : (M.carry γ).updateFlat ((c, s), ⟨t, r⟩) = (c, s) := dif_neg h
    have hR : M.updateFlat (s, ⟨t, r⟩) = s := dif_neg h
    rw [hL, hR]

end UpdateFlat

end OracleMachine

/-! ## The adversary former -/

variable {ι : ℕ → Type} [∀ n, DecidableEq (ι n)]

namespace MachineAdversary

variable {spec : (n : ℕ) → OracleSpec.{0, 0} (ι n)} {α β γ : ℕ → Type}
  {bd : BoundaryData spec α β}

/-- Reassociating the append encoding of a carried state/answer pair: the input
recode equation for the carried adversary's update witness. -/
private theorem carry_encIn_update (e : BitEncFam γ) (D : MachineAdversary bd) (n : ℕ)
    (q : (γ n × (D.M n).State) × ((t : ι n) × (spec n).Range t)) :
    ((e.pairFix D.state).pairVar bd.eIface.encAns).enc n q =
      (e.pairFix (D.state.pairVar bd.eIface.encAns)).enc n (q.1.1, (q.1.2, q.2)) := by
  obtain ⟨⟨c, s⟩, a⟩ := q
  simp only [StrEncFam.pairVar_enc, BitEncFam.pairFix_enc, List.append_assoc]

/-- Carry a fixed-width value through an adversary, at boundary
`⟨e.pair bd.eIn, e.pair bd.eOut, bd.eIface⟩`: the carried block `e` is prefixed to the
input, state, and output encodings, and the four step witnesses are the frontier
combinators — `underPrefix` for init and update (the latter recoded along append
associativity and `OracleMachine.updateFlat_carry`), `dropFix` for expose, and
`underPrefix` composed with `optionUnder` for the optional readout. -/
noncomputable def carry (e : BitEncFam γ) (D : MachineAdversary bd) :
    MachineAdversary ⟨e.pair bd.eIn, e.pair bd.eOut, bd.eIface⟩ where
  M n := (D.M n).carry (γ n)
  steps := D.steps
  stable n := OracleMachine.stableOutput_carry (D.stable n)
  state := e.pairFix D.state
  initF := .underPrefix e bd.eIn.toStrEncFam D.state D.initF
  exposeF := .dropFix e D.state D.exposeF
  updateF := (EncPolyTimeFam.underPrefix e (D.state.pairVar bd.eIface.encAns) D.state
      D.updateF).recode
    (fun n (q : (γ n × (D.M n).State) × ((t : ι n) × (spec n).Range t)) =>
      (q.1.1, (q.1.2, q.2)))
    (fun n => ((D.M n).carry (γ n)).updateFlat)
    (carry_encIn_update e D)
    (fun n q => congrArg ((e.pairFix D.state).enc n) (OracleMachine.updateFlat_carry q))
  outputF := ((EncPolyTimeFam.underPrefix e D.state (bd.eOut.option).toStrEncFam
      D.outputF).comp (.optionUnder e bd.eOut)).copy
    (fun n => ((D.M n).carry (γ n)).output) (fun _ _ => rfl)

@[simp] theorem carry_M (e : BitEncFam γ) (D : MachineAdversary bd) (n : ℕ) :
    (D.carry e).M n = (D.M n).carry (γ n) := rfl

@[simp] theorem carry_steps (e : BitEncFam γ) (D : MachineAdversary bd) :
    (D.carry e).steps = D.steps := rfl

/-- The carried adversary implements the strength-mapped program family: the carried
component is paired with every result of the underlying family. -/
theorem carry_implements (e : BitEncFam γ) {D : MachineAdversary bd}
    {oa : (n : ℕ) → α n → OracleComp (spec n) (β n)} (h : D ⊨ oa) :
    D.carry e ⊨ fun n (p : γ n × α n) => (p.1, ·) <$> oa n p.2 :=
  fun n => (h n).carry

end MachineAdversary

/-- **`OracleComp.IsPolyTime` is closed under the carry (strength) former**: pairing a
fixed-width value through a polynomial-time family is polynomial time, at the boundary
that prefixes the carried block `e` to both the input and output encodings. This is the
"a value crosses an oracle-using phase" primitive of the reduction pipeline. -/
theorem OracleComp.IsPolyTime.carry {spec : (n : ℕ) → OracleSpec.{0, 0} (ι n)}
    {α β γ : ℕ → Type} {bd : BoundaryData spec α β}
    {oa : (n : ℕ) → α n → OracleComp (spec n) (β n)}
    (hoa : OracleComp.IsPolyTime bd oa) (e : BitEncFam γ) :
    OracleComp.IsPolyTime ⟨e.pair bd.eIn, e.pair bd.eOut, bd.eIface⟩
      (fun n (p : γ n × α n) => (p.1, ·) <$> oa n p.2) := by
  obtain ⟨w⟩ := hoa
  exact ⟨{
    A := w.A.carry e
    implements := MachineAdversary.carry_implements e w.implements
    queryBound := fun n p =>
      (isQueryBound_map_iff _ _ _ _ _).mpr (w.queryBound n p.2) }⟩
