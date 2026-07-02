/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import ToMathlib.Computability.CslibPolyTime

/-!
# Base Polynomial-Time Machines

Concrete single-tape machines witnessing polynomial-time computability of basic
functions, in Cslib's `Turing.SingleTapeTM` model:

- `Turing.SingleTapeTM.clearComputer` / `Turing.SingleTapeTM.constComputer`: erase the
  input and produce a fixed output string, giving `constPolyTimeComputable` and the
  encoding-level witness `Computability.EncPolyTime.const` for constant functions.

The machines follow one design: **clear the input moving right, then write the output
backwards moving left**. Clearing onto an empty left stack keeps the tape in canonical
form (`StackTape` normalizes blanks), and writing the output back-to-front while moving
left lands the head on its first symbol, which is exactly the halting configuration
`BiTape.mk₁` — no rewind phases are needed.

Remaining base machines (symbol relabeling with a constant prefix, and projections with
respect to paired encodings) follow the same skeleton and are future work; together
with `EncPolyTime.comp` (from Cslib's proven machine composition) they discharge the
witness hypotheses of `OracleComp.isPolyTime_pure_of_witnesses` generically.
-/

@[expose] public section

universe u v

namespace Turing.SingleTapeTM

open Relation

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]

/-! ## The machines -/

/-- Erase the input moving right, then halt: computes the constant `[]`. -/
def clearComputer : SingleTapeTM Symbol where
  State := Unit
  q₀ := ()
  tr _ h := match h with
    | some _ => ⟨⟨none, some .right⟩, some ()⟩
    | none => ⟨⟨none, none⟩, none⟩

/-- Erase the input moving right, then write `o :: os` backwards moving left: computes
the constant `o :: os`. State `.inl ()` is the clearing phase; state `.inr i` writes
symbol `i` of the output next. -/
def constComputer (o : Symbol) (os : List Symbol) : SingleTapeTM Symbol where
  State := Unit ⊕ Fin (o :: os).length
  q₀ := .inl ()
  tr q h := match q with
    | .inl () => match h with
      | some _ => ⟨⟨none, some .right⟩, some (.inl ())⟩
      | none => ⟨⟨none, none⟩, some (.inr ⟨os.length, by simp⟩)⟩
    | .inr i => ⟨⟨some (o :: os)[i], if i.val = 0 then none else some .left⟩,
        if i.val = 0 then none else some (.inr ⟨i.val - 1, by omega⟩)⟩

/-! ## Clearing-phase verification -/

omit [Inhabited Symbol] [Fintype Symbol] in
private lemma bitape_head_tail_eq_mk₁ (t : List Symbol) :
    (⟨(StackTape.mapSome t).head, ∅, (StackTape.mapSome t).tail⟩ : BiTape Symbol) =
      .mk₁ t := by
  cases t with
  | nil => rfl
  | cons a as => rfl

private lemma clearComputer_clear_steps (l : List Symbol) :
    RelatesInSteps (clearComputer (Symbol := Symbol)).TransitionRelation
      ⟨some (), .mk₁ l⟩ ⟨some (), .nil⟩ l.length := by
  induction l with
  | nil => exact .refl _
  | cons c t ih =>
    refine .head _ ⟨some (), .mk₁ t⟩ _ _ ?_ ih
    show (clearComputer (Symbol := Symbol)).step ⟨some (), .mk₁ (c :: t)⟩ = _
    rw [← bitape_head_tail_eq_mk₁ t]
    rfl

private lemma constComputer_clear_steps (o : Symbol) (os l : List Symbol) :
    RelatesInSteps (constComputer o os).TransitionRelation
      ⟨some (.inl ()), .mk₁ l⟩ ⟨some (.inl ()), .nil⟩ l.length := by
  induction l with
  | nil => exact .refl _
  | cons c t ih =>
    refine .head _ ⟨some (.inl ()), .mk₁ t⟩ _ _ ?_ ih
    show (constComputer o os).step ⟨some (.inl ()), .mk₁ (c :: t)⟩ = _
    rw [← bitape_head_tail_eq_mk₁ t]
    rfl

/-! ## Writing-phase verification -/

private lemma constComputer_enter_step (o : Symbol) (os : List Symbol) :
    (constComputer o os).TransitionRelation ⟨some (.inl ()), .nil⟩
      ⟨some (.inr ⟨os.length, by simp⟩),
        ⟨none, ∅, .mapSome ((o :: os).drop (os.length + 1))⟩⟩ := by
  show (constComputer o os).step _ = _
  rw [show (o :: os).drop (os.length + 1) = [] by simp]
  rfl

private lemma constComputer_write_steps (o : Symbol) (os : List Symbol) (i : ℕ) :
    ∀ (hi : i < (o :: os).length),
      RelatesInSteps (constComputer o os).TransitionRelation
        ⟨some (.inr ⟨i, hi⟩), ⟨none, ∅, .mapSome ((o :: os).drop (i + 1))⟩⟩
        ⟨none, .mk₁ (o :: os)⟩ (i + 1) := by
  induction i with
  | zero =>
    intro hi
    refine .single ?_
    show (constComputer o os).step _ = _
    rfl
  | succ i ih =>
    intro hi
    refine .head _ ⟨some (.inr ⟨i, by omega⟩),
      ⟨none, ∅, .mapSome ((o :: os).drop (i + 1))⟩⟩ _ _ ?_ (ih (by omega))
    show (constComputer o os).step _ = _
    rw [List.drop_eq_getElem_cons hi]
    rfl

/-! ## Assembly -/

/-- Constant functions are machine-computable in linear time. -/
def constTimeComputable : (out : List Symbol) →
    TimeComputable (Symbol := Symbol) (fun _ => out)
  | [] =>
    { tm := clearComputer
      timeBound := fun n => n + 1
      outputsFunInTime := fun l => by
        refine ⟨l.length + 1, le_rfl, ?_⟩
        exact RelatesInSteps.tail
          (r := (clearComputer (Symbol := Symbol)).TransitionRelation)
          ⟨some (), .mk₁ l⟩ ⟨some (), .nil⟩ ⟨none, .mk₁ []⟩ _
          (clearComputer_clear_steps l) rfl }
  | o :: os =>
    { tm := constComputer o os
      timeBound := fun n => n + (os.length + 2)
      outputsFunInTime := fun l => by
        refine ⟨l.length + (1 + (os.length + 1)), by omega, ?_⟩
        exact (constComputer_clear_steps o os l).trans
          ((RelatesInSteps.single (constComputer_enter_step o os)).trans
            (constComputer_write_steps o os os.length (by simp))) }

/-- Constant functions are machine-computable in polynomial time. -/
noncomputable def constPolyTimeComputable (out : List Symbol) :
    PolyTimeComputable (Symbol := Symbol) (fun _ => out) where
  toTimeComputable := constTimeComputable out
  poly := .X + .C (out.length + 2)
  bounds n := by
    cases out with
    | nil =>
      simp only [constTimeComputable, Polynomial.eval_add, Polynomial.eval_X,
        Polynomial.eval_C, List.length_nil]
      omega
    | cons o os =>
      simp only [constTimeComputable, Polynomial.eval_add, Polynomial.eval_X,
        Polynomial.eval_C, List.length_cons]
      omega

end Turing.SingleTapeTM

namespace Computability.EncPolyTime

/-- Constant functions are polynomial-time computable relative to any encodings. -/
noncomputable def const {α : Type u} {β : Type v} (ea : α → List Bool)
    (eb : β → List Bool) (c : β) : EncPolyTime ea eb (fun _ => c) where
  toFun _ := eb c
  polyTime := Turing.SingleTapeTM.constPolyTimeComputable (eb c)
  map_encode _ := rfl

end Computability.EncPolyTime
