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
- `Turing.SingleTapeTM.tableComputer`: read the input into machine state through the
  prefix tree of a finite set of valid inputs, then write the corresponding table
  output, giving `tablePolyTimeComputable` and the encoding-level witness
  `Computability.EncPolyTime.ofFintype`: **any function with a finite domain is
  polynomial-time computable** relative to an injective encoding — but with a
  description size (`EncPolyTime.size_ofFintype_le`) that grows with the domain's
  total encoded length, so a *family* of tables stays within a polynomial advice
  bound (`PolyTimeAdversary.descBound`) only on domains of polynomially bounded
  cardinality. Within that regime it subsumes constants, relabelings, and projections,
  and discharges all four per-step machine witnesses of `PolyTimeAdversary` for
  small-state oracle machines.

The machines follow one design: **clear the input moving right, then write the output
backwards moving left**. Clearing onto an empty left stack keeps the tape in canonical
form (`StackTape` normalizes blanks), and writing the output back-to-front while moving
left lands the head on its first symbol, which is exactly the halting configuration
`BiTape.mk₁` — no rewind phases are needed.

Base machines for *unbounded* domains (symbol relabeling, projections with respect to
paired encodings of infinite types) would follow the same skeleton and remain future
work; together with `EncPolyTime.comp` (from Cslib's proven machine composition) they
would extend the generic witnesses beyond finite domains. The declared frontier of
those combinators — stated in the raw-encoding family form
(`Computability.EncPolyTimeFam`) that the adversary layer consumes — is
`ToMathlib.Computability.MachineCombinators`.
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
    change (clearComputer (Symbol := Symbol)).step ⟨some (), .mk₁ (c :: t)⟩ = _
    rw [← bitape_head_tail_eq_mk₁ t]
    rfl

private lemma constComputer_clear_steps (o : Symbol) (os l : List Symbol) :
    RelatesInSteps (constComputer o os).TransitionRelation
      ⟨some (.inl ()), .mk₁ l⟩ ⟨some (.inl ()), .nil⟩ l.length := by
  induction l with
  | nil => exact .refl _
  | cons c t ih =>
    refine .head _ ⟨some (.inl ()), .mk₁ t⟩ _ _ ?_ ih
    change (constComputer o os).step ⟨some (.inl ()), .mk₁ (c :: t)⟩ = _
    rw [← bitape_head_tail_eq_mk₁ t]
    rfl

/-! ## Writing-phase verification -/

private lemma constComputer_enter_step (o : Symbol) (os : List Symbol) :
    (constComputer o os).TransitionRelation ⟨some (.inl ()), .nil⟩
      ⟨some (.inr ⟨os.length, by simp⟩),
        ⟨none, ∅, .mapSome ((o :: os).drop (os.length + 1))⟩⟩ := by
  change (constComputer o os).step _ = _
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
    change (constComputer o os).step _ = _
    rfl
  | succ i ih =>
    intro hi
    refine .head _ ⟨some (.inr ⟨i, by omega⟩),
      ⟨none, ∅, .mapSome ((o :: os).drop (i + 1))⟩⟩ _ _ ?_ (ih (by omega))
    change (constComputer o os).step _ = _
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

/-- The constant-function machine has at most `out.length + 2` states: one clearing
state plus one writing state per output symbol. -/
theorem size_constPolyTimeComputable_le (out : List Symbol) :
    (constPolyTimeComputable (Symbol := Symbol) out).size ≤ out.length + 2 := by
  cases out with
  | nil =>
    show Fintype.card Unit ≤ 2
    simp
  | cons o os =>
    show Fintype.card (Unit ⊕ Fin (o :: os).length) ≤ (o :: os).length + 2
    simp only [Fintype.card_sum, Fintype.card_unit, Fintype.card_fin, List.length_cons]
    omega

/-! ## The finite-table machine

A machine computing `fun l => if l ∈ S then T l else []` for a *finite* set `S` of
valid inputs: read the input into machine state through the prefix tree of `S`
(clearing as it goes), then on the blank look up the table and write the output
backwards moving left exactly as `constComputer` does. Inputs that stop matching any
prefix of `S` fall into an absorbing junk state and clear to a blank tape. -/

section Table

variable [DecidableEq Symbol]

omit [Inhabited Symbol] [Fintype Symbol] [DecidableEq Symbol] in
private lemma bitape_mk₁_eq_of_length_pos {t : List Symbol} (h : 0 < t.length) :
    (BiTape.mk₁ t : BiTape Symbol) = ⟨some t[0], ∅, .mapSome (t.drop 1)⟩ := by
  cases t with
  | nil => simp at h
  | cons a as => rfl

omit [Inhabited Symbol] [Fintype Symbol] in
/-- All prefixes of members of `S`: the reading states of `tableComputer`. -/
def prefixClosure (S : Finset (List Symbol)) : Finset (List Symbol) :=
  S.biUnion fun s => s.inits.toFinset

omit [Inhabited Symbol] [Fintype Symbol] in
theorem mem_prefixClosure {S : Finset (List Symbol)} {l : List Symbol} :
    l ∈ prefixClosure S ↔ ∃ s ∈ S, l <+: s := by
  simp [prefixClosure, List.mem_inits]

omit [Inhabited Symbol] [Fintype Symbol] in
theorem subset_prefixClosure (S : Finset (List Symbol)) : S ⊆ prefixClosure S :=
  fun s hs => mem_prefixClosure.mpr ⟨s, hs, List.prefix_refl s⟩

omit [Inhabited Symbol] [Fintype Symbol] in
/-- Path independence of falling out of the prefix tree: once the consumed prefix
matches no member of `S`, no extension does either. -/
theorem append_not_mem_prefixClosure {S : Finset (List Symbol)} {l : List Symbol}
    (h : l ∉ prefixClosure S) (b : Symbol) : l ++ [b] ∉ prefixClosure S := by
  intro hmem
  obtain ⟨s, hs, hpre⟩ := mem_prefixClosure.mp hmem
  exact h (mem_prefixClosure.mpr ⟨s, hs, (List.prefix_append l [b]).trans hpre⟩)

omit [Inhabited Symbol] [Fintype Symbol] in
/-- States of the finite-table machine: reading (tracking the consumed prefix through
the prefix tree of `S`), junk (clearing an unmatched input), or writing symbol `i` of
the table output of `s`. -/
abbrev TableState (S : Finset (List Symbol)) (T : List Symbol → List Symbol) : Type :=
  ({l // l ∈ prefixClosure S} ⊕ Unit) ⊕ (Σ s : {s // s ∈ S}, Fin (T s.1).length)

omit [Inhabited Symbol] [Fintype Symbol] in
/-- The state after consuming the prefix `l`: still reading if `l` can extend to a
member of `S`, junk otherwise. Totality in `l` makes the reading-step lemma uniform
(via `append_not_mem_prefixClosure`). -/
def readState (S : Finset (List Symbol)) (T : List Symbol → List Symbol)
    (l : List Symbol) : TableState S T :=
  if h : l ∈ prefixClosure S then .inl (.inl ⟨l, h⟩) else .inl (.inr ())

omit [Inhabited Symbol] [Fintype Symbol] in
/-- The state entered on reaching the blank at the end of the input with consumed
prefix `l`: write the table output backwards if `l ∈ S` and the output is nonempty,
otherwise halt (the tape is already the blank output). -/
def enterState (S : Finset (List Symbol)) (T : List Symbol → List Symbol)
    (l : List Symbol) : Option (TableState S T) :=
  if hS : l ∈ S then
    if hT : (T l).length = 0 then none
    else some (.inr ⟨⟨l, hS⟩,
      ⟨(T l).length - 1, by change (T l).length - 1 < (T l).length; omega⟩⟩)
  else none

/-- The finite-table machine: clear the input moving right while tracking the consumed
prefix through the prefix tree of `S`; on the blank, look up the table and write the
output backwards moving left. Computes `fun l => if l ∈ S then T l else []`. -/
def tableComputer (S : Finset (List Symbol)) (T : List Symbol → List Symbol) :
    SingleTapeTM Symbol where
  State := TableState S T
  q₀ := readState S T []
  tr q h := match q with
    | .inl (.inl ⟨l, _⟩) => match h with
      | some b => ⟨⟨none, some .right⟩, some (readState S T (l ++ [b]))⟩
      | none => ⟨⟨none, none⟩, enterState S T l⟩
    | .inl (.inr ()) => match h with
      | some _ => ⟨⟨none, some .right⟩, some (.inl (.inr ()))⟩
      | none => ⟨⟨none, none⟩, none⟩
    | .inr ⟨s, i⟩ => ⟨⟨some (T s.1)[i], if i.val = 0 then none else some .left⟩,
        if i.val = 0 then none else some (.inr ⟨s, ⟨i.val - 1, by omega⟩⟩)⟩

/-! ### Reading-phase verification -/

private lemma tableComputer_read_step (S : Finset (List Symbol))
    (T : List Symbol → List Symbol) (l : List Symbol) (b : Symbol) (t : List Symbol) :
    (tableComputer S T).TransitionRelation
      ⟨some (readState S T l), .mk₁ (b :: t)⟩
      ⟨some (readState S T (l ++ [b])), .mk₁ t⟩ := by
  change (tableComputer S T).step _ = _
  rw [← bitape_head_tail_eq_mk₁ t]
  by_cases h : l ∈ prefixClosure S
  · simp only [readState]
    rw [dif_pos h]
    rfl
  · simp only [readState]
    rw [dif_neg h, dif_neg (append_not_mem_prefixClosure h b)]
    rfl

private lemma tableComputer_read_steps (S : Finset (List Symbol))
    (T : List Symbol → List Symbol) (t l : List Symbol) :
    RelatesInSteps (tableComputer S T).TransitionRelation
      ⟨some (readState S T l), .mk₁ t⟩ ⟨some (readState S T (l ++ t)), .nil⟩
      t.length := by
  induction t generalizing l with
  | nil => rw [List.append_nil]; exact .refl _
  | cons b t ih =>
    refine .head _ ⟨some (readState S T (l ++ [b])), .mk₁ t⟩ _ _
      (tableComputer_read_step S T l b t) ?_
    have h := ih (l ++ [b])
    rwa [← List.append_cons] at h

/-! ### Lookup and writing-phase verification -/

private lemma tableComputer_blank_step (S : Finset (List Symbol))
    (T : List Symbol → List Symbol) (l : List Symbol) :
    (tableComputer S T).TransitionRelation
      ⟨some (readState S T l), .nil⟩ ⟨enterState S T l, .nil⟩ := by
  change (tableComputer S T).step _ = _
  by_cases h : l ∈ prefixClosure S
  · simp only [readState]
    rw [dif_pos h]
    rfl
  · simp only [readState, enterState]
    rw [dif_neg h, dif_neg fun hS => h (subset_prefixClosure S hS)]
    rfl

private lemma tableComputer_write_steps (S : Finset (List Symbol))
    (T : List Symbol → List Symbol) (s : {s // s ∈ S}) (i : ℕ) :
    ∀ (hi : i < (T s.1).length),
      RelatesInSteps (tableComputer S T).TransitionRelation
        ⟨some (.inr ⟨s, ⟨i, hi⟩⟩), ⟨none, ∅, .mapSome ((T s.1).drop (i + 1))⟩⟩
        ⟨none, .mk₁ (T s.1)⟩ (i + 1) := by
  induction i with
  | zero =>
    intro hi
    refine .single ?_
    change (tableComputer S T).step _ = _
    rw [bitape_mk₁_eq_of_length_pos hi]
    rfl
  | succ i ih =>
    intro hi
    refine .head _ ⟨some (.inr ⟨s, ⟨i, by omega⟩⟩),
      ⟨none, ∅, .mapSome ((T s.1).drop (i + 1))⟩⟩ _ _ ?_ (ih (by omega))
    change (tableComputer S T).step _ = _
    rw [List.drop_eq_getElem_cons hi]
    rfl

private lemma tableComputer_finish_within (S : Finset (List Symbol))
    (T : List Symbol → List Symbol) (l : List Symbol) :
    RelatesWithinSteps (tableComputer S T).TransitionRelation
      ⟨some (readState S T l), .nil⟩
      ⟨none, .mk₁ (if l ∈ S then T l else [])⟩
      ((S.sup fun s => (T s).length) + 1) := by
  have h1 := tableComputer_blank_step S T l
  simp only [enterState] at h1
  by_cases hS : l ∈ S
  · by_cases hT : (T l).length = 0
    · rw [dif_pos hS, dif_pos hT] at h1
      rw [if_pos hS, List.length_eq_zero_iff.mp hT]
      exact RelatesWithinSteps.of_le (.single h1) (by omega)
    · rw [dif_pos hS, dif_neg hT] at h1
      rw [if_pos hS]
      have h2 := tableComputer_write_steps S T ⟨l, hS⟩ ((T l).length - 1)
        (by change (T l).length - 1 < (T l).length; omega)
      rw [show (T l).length - 1 + 1 = (T l).length from by omega,
        List.drop_length] at h2
      refine RelatesWithinSteps.of_le
        ((RelatesWithinSteps.single h1).trans
          (RelatesWithinSteps.of_relatesInSteps h2)) ?_
      have hle : (T l).length ≤ S.sup fun s => (T s).length :=
        Finset.le_sup (f := fun s => (T s).length) hS
      omega
  · rw [dif_neg hS] at h1
    rw [if_neg hS]
    exact RelatesWithinSteps.of_le (.single h1) (by omega)

/-! ### Assembly -/

/-- Finite tables are machine-computable in linear time: `n` steps to read the input
into state, then at most one plus the longest table output to write the result. -/
def tableTimeComputable (S : Finset (List Symbol)) (T : List Symbol → List Symbol) :
    TimeComputable (Symbol := Symbol) (fun l => if l ∈ S then T l else []) where
  tm := tableComputer S T
  timeBound n := n + ((S.sup fun s => (T s).length) + 1)
  outputsFunInTime l := by
    exact (RelatesWithinSteps.of_relatesInSteps
      (tableComputer_read_steps S T l [])).trans (tableComputer_finish_within S T l)

/-- Finite tables are machine-computable in polynomial time. -/
noncomputable def tablePolyTimeComputable (S : Finset (List Symbol))
    (T : List Symbol → List Symbol) :
    PolyTimeComputable (Symbol := Symbol) (fun l => if l ∈ S then T l else []) where
  toTimeComputable := tableTimeComputable S T
  poly := .X + .C ((S.sup fun s => (T s).length) + 1)
  bounds n := by
    simp only [tableTimeComputable, Polynomial.eval_add, Polynomial.eval_X,
      Polynomial.eval_C]
    omega

/-! ### Description size of the table machine

The table machine's *time* is linear, but its *state count* — the reading prefix tree
plus the writing states — grows with the total length of the valid inputs and their
table outputs. This is the advice a table smuggles: a family of tables over
exponentially large domains has exponential description size, which is why witness
families must carry an explicit size bound (`Computability.EncPolyTime.size`). -/

omit [Inhabited Symbol] [Fintype Symbol] in
/-- The prefix tree of a finite set of strings has at most `∑ (length + 1)` nodes. -/
theorem card_prefixClosure_le (S : Finset (List Symbol)) :
    (prefixClosure S).card ≤ ∑ s ∈ S, (s.length + 1) :=
  Finset.card_biUnion_le.trans (Finset.sum_le_sum fun s _ =>
    (List.toFinset_card_le _).trans (by simp))

omit [Inhabited Symbol] [Fintype Symbol] in
/-- The state count of the finite-table machine: prefix-tree nodes, the junk state, and
one writing state per output symbol. -/
theorem card_tableState (S : Finset (List Symbol)) (T : List Symbol → List Symbol) :
    Fintype.card (TableState S T) =
      ((prefixClosure S).card + 1) + ∑ s ∈ S, (T s).length := by
  simp [TableState, Fintype.card_sigma, Finset.sum_attach S fun s => (T s).length]

end Table

end Turing.SingleTapeTM

namespace Computability.EncPolyTime

/-- Constant functions are polynomial-time computable relative to any encodings. -/
noncomputable def const {α : Type u} {β : Type v} (ea : α → List Bool)
    (eb : β → List Bool) (c : β) : EncPolyTime ea eb (fun _ => c) where
  toFun _ := eb c
  polyTime := Turing.SingleTapeTM.constPolyTimeComputable (eb c)
  map_encode _ := rfl

/-- **Any function with a finite domain is polynomial-time computable** relative to an
injective input encoding: the machine reads the input into state through the prefix
tree of the finitely many valid encodings, then writes the encoded output. The trade is
time for description: the machine has one reading state per prefix of a valid input
(`size_ofFintype_le`), so families of these witnesses respect a polynomial advice bound
only on domains of polynomially bounded cardinality. Instantiated at the `boolify` of a
`FinEncoding` (injective by `FinEncoding.boolify_injective`), this discharges the
per-step machine witnesses of small-state oracle machines. -/
noncomputable def ofFintype {α : Type u} {β : Type v} [Fintype α]
    (ea : α → List Bool) (hea : Function.Injective ea) (eb : β → List Bool)
    (f : α → β) : EncPolyTime ea eb f where
  toFun l := if l ∈ Finset.univ.image ea
    then ((Function.partialInv ea l).map fun a => eb (f a)).getD [] else []
  polyTime := Turing.SingleTapeTM.tablePolyTimeComputable (Finset.univ.image ea)
    fun l => ((Function.partialInv ea l).map fun a => eb (f a)).getD []
  map_encode a := by
    rw [if_pos (Finset.mem_image_of_mem ea (Finset.mem_univ a)),
      Function.partialInv_left hea]
    rfl

/-- The finite-table witness runs in time linear in the input plus the longest encoded
output: with a pointwise bound `B` on the output encodings, evaluation at `k` is at
most `k + (B + 1)`. This is the shape that discharges the uniform per-step time bounds
of `PolyTimeAdversary`. -/
theorem time_ofFintype_eval_le {α : Type u} {β : Type v} [Fintype α]
    {ea : α → List Bool} (hea : Function.Injective ea) {eb : β → List Bool}
    {f : α → β} {B : ℕ} (hB : ∀ a, (eb (f a)).length ≤ B) (k : ℕ) :
    (ofFintype ea hea eb f).time.eval k ≤ k + (B + 1) := by
  have htime : (ofFintype ea hea eb f).time =
      .X + .C (((Finset.univ.image ea).sup fun l =>
        (((Function.partialInv ea l).map fun a => eb (f a)).getD []).length) + 1) := rfl
  have hsup : ((Finset.univ.image ea).sup fun l =>
      (((Function.partialInv ea l).map fun a => eb (f a)).getD []).length) ≤ B := by
    refine Finset.sup_le fun l hl => ?_
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hl
    rw [Function.partialInv_left hea]
    exact hB a
  rw [htime, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
  omega

/-- The constant-function witness has at most `(eb c).length + 2` machine states. -/
theorem size_const_le {α : Type u} {β : Type v} (ea : α → List Bool)
    (eb : β → List Bool) (c : β) :
    (const ea eb c).size ≤ (eb c).length + 2 :=
  Turing.SingleTapeTM.size_constPolyTimeComputable_le (eb c)

/-- The description size of the finite-table witness: the machine hard-codes the whole
input/output table, so its state count grows with the **total encoded length of the
domain** — for a domain of exponential cardinality this is exponential advice, however
fast the machine runs. Families of `ofFintype` witnesses are therefore only usable
where the domain cardinality is polynomially bounded in the security parameter. -/
theorem size_ofFintype_le {α : Type u} {β : Type v} [Fintype α]
    {ea : α → List Bool} (hea : Function.Injective ea) (eb : β → List Bool)
    (f : α → β) :
    (ofFintype ea hea eb f).size ≤
      (∑ a : α, ((ea a).length + 1)) + 1 + ∑ a : α, (eb (f a)).length := by
  show Fintype.card (Turing.SingleTapeTM.TableState (Finset.univ.image ea)
    fun l => ((Function.partialInv ea l).map fun a => eb (f a)).getD []) ≤ _
  rw [Turing.SingleTapeTM.card_tableState]
  have hinj : ∀ a ∈ Finset.univ, ∀ b ∈ Finset.univ, ea a = ea b → a = b :=
    fun a _ b _ h => hea h
  have h1 : (Turing.SingleTapeTM.prefixClosure (Finset.univ.image ea)).card ≤
      ∑ a : α, ((ea a).length + 1) := by
    refine (Turing.SingleTapeTM.card_prefixClosure_le _).trans (le_of_eq ?_)
    rw [Finset.sum_image hinj]
  have h2 : (∑ s ∈ Finset.univ.image ea,
      (((Function.partialInv ea s).map fun a => eb (f a)).getD []).length) =
      ∑ a : α, (eb (f a)).length := by
    rw [Finset.sum_image hinj]
    exact Finset.sum_congr rfl fun a _ => by rw [Function.partialInv_left hea]; rfl
  omega

/-- Discharge form of `size_ofFintype_le`: a cardinality bound on the domain and
pointwise bounds on both encodings give the table size bound consumed by
`PolyTimeAdversary.descBound` fields. -/
theorem size_ofFintype_le_of_bounds {α : Type u} {β : Type v} [Fintype α]
    {ea : α → List Bool} (hea : Function.Injective ea) {eb : β → List Bool}
    {f : α → β} {A La B : ℕ} (hcard : Fintype.card α ≤ A)
    (hla : ∀ a, (ea a).length ≤ La) (hB : ∀ a, (eb (f a)).length ≤ B) :
    (ofFintype ea hea eb f).size ≤ A * (La + 1 + B) + 1 := by
  refine (size_ofFintype_le hea eb f).trans ?_
  have h1 : (∑ a : α, ((ea a).length + 1)) ≤ Fintype.card α * (La + 1) := by
    refine (Finset.sum_le_card_nsmul _ _ (La + 1) fun a _ => ?_).trans_eq (by
      simp [smul_eq_mul])
    have := hla a; omega
  have h2 : (∑ a : α, (eb (f a)).length) ≤ Fintype.card α * B := by
    refine (Finset.sum_le_card_nsmul _ _ B fun a _ => hB a).trans_eq (by
      simp [smul_eq_mul])
  have h3 : Fintype.card α * (La + 1) ≤ A * (La + 1) := Nat.mul_le_mul_right _ hcard
  have h4 : Fintype.card α * B ≤ A * B := Nat.mul_le_mul_right _ hcard
  calc (∑ a : α, ((ea a).length + 1)) + 1 + ∑ a : α, (eb (f a)).length
      ≤ A * (La + 1) + 1 + A * B := by omega
    _ = A * (La + 1 + B) + 1 := by ring

end Computability.EncPolyTime
