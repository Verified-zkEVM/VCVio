/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import ToMathlib.Computability.BitEncoding
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Data.FinEnum

/-!
# Counting Polynomial-Size Turing Machines

The combinatorial core of the non-triviality certificate for the machine-grounded
polynomial-time model (`VCVio.OracleComp.Coinductive.PolyTimeNontrivial`): only
sub-doubly-exponentially many predicates `BitVec n → Bool` are realizable by
`d`-state single-tape machines, while there are `2 ^ (2 ^ n)` such predicates.

The pieces, each isolated so the diagonalization argument reads as pure counting:

* **Canonical `d`-state machines** (`Cslib.Turing.SingleTapeTM.TMTable`): a transition table
  `Fin d → Option Bool → Stmt Bool × Option (Fin d)` together with an initial state.
  These are a `Fintype` with an explicit, provable cardinality
  (`card_tmTable`, bounded by `Cslib.Turing.SingleTapeTM.B`), and `reify` packages one back
  into a `SingleTapeTM Bool`. The `Fintype`/`DecidableEq` instances for the underlying
  `Turing.Dir` and `SingleTapeTM.Stmt Bool` are supplied here.
* **State normalization** (`exists_tmTable_of_card_le`): any
  `SingleTapeTM Bool` with at most `d` states computes the same string function as
  `reify` of some `TMTable d`.
* **Realizable predicates** (`Computability.RealizableLE`): the predicates realizable by
  an input/output `EncPolyTime` pair of description size at most `d`. This set is covered
  by a `Finset` of cardinality at most `B d ^ 2` (`exists_realizableLE_covering`, the
  counting core: the cover of `RealizableLE n d` by the image of
  `TMTable d × TMTable d` under `tablePairPred`, built from state normalization), and it is
  monotone in `d` (`realizableLE_mono`).
* **Growth bounds**: every polynomial is eventually dominated by `2 ^ (n / 4)`
  (`Computability.eventually_poly_le`), while the machine count stays below the function
  count (`Computability.eventually_count_lt`).
* **The function space** has cardinality `2 ^ (2 ^ n)` (`Computability.card_bitVec_fun`),
  and a `Finset` family of subexponential cardinality misses a diagonal predicate
  eventually (`Computability.exists_diagonal`).
-/

@[expose] public section

open Filter Asymptotics

namespace Cslib.Turing.SingleTapeTM

/-! ## Finiteness of statements and directions -/

/-- A `SingleTapeTM.Stmt` is a pair of an optional write symbol and an optional move. -/
def stmtProdEquiv : SingleTapeTM.Stmt Bool ≃ (Option Bool × Option Turing.Dir) where
  toFun s := (s.symbol, s.movement)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Fintype Turing.Dir :=
  ⟨{Turing.Dir.left, Turing.Dir.right}, fun d => by cases d <;> decide⟩

instance : DecidableEq (SingleTapeTM.Stmt Bool) :=
  fun _ _ => decidable_of_iff _ stmtProdEquiv.injective.eq_iff

noncomputable instance : Fintype (SingleTapeTM.Stmt Bool) :=
  Fintype.ofEquiv _ stmtProdEquiv.symm

theorem card_dir : Fintype.card Turing.Dir = 2 := by decide

theorem card_stmt : Fintype.card (SingleTapeTM.Stmt Bool) = 9 := by
  rw [Fintype.card_congr stmtProdEquiv]; decide

/-! ## Canonical `d`-state machines -/

/-- A canonical `d`-state single-tape machine over `Bool`: a transition table on states
`Fin d` together with an initial state. Every machine with at most `d` states computes,
after relabeling, the same function as `reify` of one of these (`exists_tmTable_of_card_le`),
so `TMTable d` is the finite index of `d`-state machines used for counting. -/
abbrev TMTable (d : ℕ) : Type :=
  (Fin d → Option Bool → SingleTapeTM.Stmt Bool × Option (Fin d)) × Fin d

noncomputable instance (d : ℕ) : Fintype (TMTable d) := inferInstance

instance (d : ℕ) : DecidableEq (TMTable d) := inferInstance

/-- A crude closed-form upper bound on the number of `d`-state machines: the exact
cardinality `card_tmTable`. -/
def B (d : ℕ) : ℕ := (9 * (d + 1)) ^ (3 * d) * d

/-- The exact number of canonical `d`-state machines: each of the `d` states maps each of
the `3` head symbols (`Option Bool`) to one of the `9 * (d + 1)` statement/next-state
pairs, and there are `d` choices of initial state. -/
theorem card_tmTable (d : ℕ) : Fintype.card (TMTable d) = B d := by
  simp only [B, TMTable, Fintype.card_prod, Fintype.card_fun, card_stmt,
    Fintype.card_option, Fintype.card_fin, Fintype.card_bool, ← pow_mul]

theorem card_tmTable_le (d : ℕ) : Fintype.card (TMTable d) ≤ B d :=
  (card_tmTable d).le

/-- Package a canonical table back into a `SingleTapeTM Bool` on state space `Fin d`. -/
def reify {d : ℕ} (t : TMTable d) : SingleTapeTM Bool where
  State := Fin d
  q₀ := t.2
  tr := t.1

/-! ## State-relabeling normalization construction

The machinery discharging `exists_tmTable_of_card_le`: relabel the finite state space of a
machine `tm` through `Fintype.equivFin`, embed `Fin (card tm.State)` into `Fin d` along the
cardinality inequality (`embFin`), and transport the transition function on the image
(`normTr`), sending every spare state (those outside the image, detected by `decFin`) to a
fixed halting transition. Configurations transport along `normCfg`, single steps correspond
(`step_normCfg`), and this lifts through `ReflTransGen` in both directions
(`normCfg_reflTransGen`, `reflTransGen_normCfg_reverse`), giving the `Outputs` equivalence. -/

section Normalize

/-- Embed a finite type into `Fin d` (with `card ≤ d`) via its `Fintype.equivFin` labeling. -/
noncomputable def embFin {α : Type*} [Fintype α] {d : ℕ} (hd : Fintype.card α ≤ d) (s : α) :
    Fin d :=
  (Fintype.equivFin α s).castLE hd

/-- The partial inverse of `embFin`: recover the state whose label is `i`, or `none` for
spare indices `i` with no preimage. -/
noncomputable def decFin {α : Type*} [Fintype α] {d : ℕ} (i : Fin d) : Option α :=
  if hi : (i : ℕ) < Fintype.card α then some ((Fintype.equivFin α).symm ⟨i, hi⟩) else none

/-- `decFin` inverts `embFin` on the image. -/
lemma decFin_embFin {α : Type*} [Fintype α] {d : ℕ} (hd : Fintype.card α ≤ d) (s : α) :
    (decFin (embFin hd s) : Option α) = some s := by
  have hlt : ((embFin hd s : Fin d) : ℕ) < Fintype.card α := by
    simp only [embFin, Fin.val_castLE]; exact (Fintype.equivFin α s).isLt
  simp only [decFin, dif_pos hlt]
  congr 1
  apply (Fintype.equivFin α).symm_apply_eq.mpr
  apply Fin.ext
  simp [embFin, Fin.val_castLE]

/-- `embFin` is injective. -/
lemma embFin_injective {α : Type*} [Fintype α] {d : ℕ} (hd : Fintype.card α ≤ d) :
    Function.Injective (embFin hd) := fun _ _ hab =>
  (Fintype.equivFin α).injective (Fin.castLE_injective hd hab)

variable {d : ℕ} (tm : SingleTapeTM Bool) (emb : tm.State → Fin d)
  (dec : Fin d → Option tm.State)

/-- Transition table transporting `tm`'s transitions along `emb`; spare states (those with
`dec i = none`) are given a fixed halting transition. -/
noncomputable def normTr : Fin d → Option Bool → SingleTapeTM.Stmt Bool × Option (Fin d) :=
  fun i b =>
    match dec i with
    | some s => ((tm.tr s b).1, (tm.tr s b).2.map emb)
    | none => (default, none)

/-- The canonical `d`-state table normalizing `tm` onto `Fin d` along `emb`/`dec`. -/
noncomputable def normTable : TMTable d := (normTr tm emb dec, emb tm.q₀)

/-- Transport a configuration of `tm` to the reified normalized machine. -/
noncomputable def normCfg (c : tm.Cfg) : (reify (normTable tm emb dec)).Cfg :=
  ⟨c.state.map emb, c.BiTape⟩

variable {tm emb dec}

/-- The reified normalized machine's step transports `tm`'s step along `normCfg`, provided
`dec` inverts `emb` on the image. -/
lemma step_normCfg (hdec : ∀ s, dec (emb s) = some s) (c : tm.Cfg) :
    (reify (normTable tm emb dec)).step (normCfg tm emb dec c)
      = (tm.step c).map (normCfg tm emb dec) := by
  obtain ⟨st, tp⟩ := c
  cases st with
  | none => rfl
  | some q =>
    have hdq : dec (emb q) = some q := hdec q
    rcases htr : tm.tr q tp.head with ⟨⟨wr, dir⟩, q''⟩
    simp only [step, normCfg, reify, normTable, normTr, Option.map_some, hdq, htr]

/-- `normCfg` is injective when `emb` is. -/
lemma normCfg_injective (hemb : Function.Injective emb) :
    Function.Injective (normCfg tm emb dec) := by
  rintro ⟨s1, t1⟩ ⟨s2, t2⟩ h
  simp only [normCfg, Cfg.mk.injEq] at h
  obtain ⟨hs, ht⟩ := h
  have hss : s1 = s2 := Option.map_injective hemb hs
  subst hss; subst ht; rfl

/-- A run of `tm` maps forward to a run of the normalized machine. -/
lemma normCfg_reflTransGen (hdec : ∀ s, dec (emb s) = some s) {c c' : tm.Cfg}
    (h : Relation.ReflTransGen tm.TransitionRelation c c') :
    Relation.ReflTransGen (reify (normTable tm emb dec)).TransitionRelation
      (normCfg tm emb dec c) (normCfg tm emb dec c') := by
  have hstep : ∀ a b, tm.TransitionRelation a b →
      (reify (normTable tm emb dec)).TransitionRelation
        (normCfg tm emb dec a) (normCfg tm emb dec b) := by
    intro a b hab
    have hs := step_normCfg hdec a
    rw [show tm.step a = some b from hab, Option.map_some] at hs
    exact hs
  exact Relation.ReflTransGen.lift (normCfg tm emb dec) hstep c c' h

/-- A run of the normalized machine from an image configuration stays in the image and maps
back to a run of `tm`. -/
lemma reflTransGen_normCfg_reverse (hdec : ∀ s, dec (emb s) = some s) {c : tm.Cfg}
    {c' : (reify (normTable tm emb dec)).Cfg}
    (h : Relation.ReflTransGen (reify (normTable tm emb dec)).TransitionRelation
      (normCfg tm emb dec c) c') :
    ∃ c₂, c' = normCfg tm emb dec c₂ ∧ Relation.ReflTransGen tm.TransitionRelation c c₂ := by
  induction h with
  | refl => exact ⟨c, rfl, Relation.ReflTransGen.refl⟩
  | @tail b e hab hbc ih =>
    obtain ⟨c₂, rfl, hrun⟩ := ih
    have hs := step_normCfg hdec c₂
    rw [show (reify (normTable tm emb dec)).step (normCfg tm emb dec c₂) = some e from hbc] at hs
    obtain ⟨c₃, hstep, hc3⟩ := Option.map_eq_some_iff.mp hs.symm
    exact ⟨c₃, hc3.symm, hrun.tail hstep⟩

end Normalize

/-! ## Determinism of machine runs

Supporting facts for `Computability.exists_realizableLE_covering`: a single-tape machine
is deterministic (its `step` is a function), so the output list of a halting run is
unique. This lets the covering predicate attached to a table pair be read off by an
unbounded-search-free choice construction and still agree with any witness predicate. -/

section Determinism

/-- In a relation that is a partial function (deterministic), two irreducible points
reachable from a common source coincide. -/
theorem _root_.Relation.ReflTransGen.unique_of_deterministic
    {α : Type*} {R : α → α → Prop}
    (hdet : ∀ {a b c : α}, R a b → R a c → b = c)
    {a b c : α} (hb : Relation.ReflTransGen R a b) (hc : Relation.ReflTransGen R a c)
    (hbf : ∀ y, ¬ R b y) (hcf : ∀ y, ¬ R c y) : b = c := by
  induction hb using Relation.ReflTransGen.head_induction_on with
  | refl =>
      rcases hc.cases_head with h | ⟨y, hy, _⟩
      · exact h
      · exact absurd hy (hbf y)
  | head h' _ ih =>
      rename_i a' _
      rcases hc.cases_head with h | ⟨y, hy, hyc⟩
      · exact absurd (h ▸ h') (hcf a')
      · rw [hdet h' hy] at ih; exact ih hyc

/-- Distinct input lists give distinct initial/halting tapes: `BiTape.mk₁` is injective. -/
theorem _root_.Cslib.Turing.BiTape.mk₁_injective {Symbol : Type} :
    Function.Injective (Cslib.Turing.BiTape.mk₁ : List Symbol → Cslib.Turing.BiTape Symbol) := by
  intro l₁ l₂ h
  cases l₁ with
  | nil =>
    cases l₂ with
    | nil => rfl
    | cons b t => simp [Cslib.Turing.BiTape.mk₁, Cslib.Turing.BiTape.nil] at h
  | cons a s =>
    cases l₂ with
    | nil => simp [Cslib.Turing.BiTape.mk₁, Cslib.Turing.BiTape.nil] at h
    | cons b t =>
      simp only [Cslib.Turing.BiTape.mk₁, Cslib.Turing.BiTape.mk.injEq, Option.some.injEq] at h
      obtain ⟨hab, -, hst⟩ := h
      have : (s.map some) = (t.map some) := by
        have := congrArg Cslib.Turing.StackTape.toList hst
        simpa [Cslib.Turing.StackTape.mapSome] using this
      have hst' : s = t := List.map_injective_iff.mpr (Option.some_injective _) this
      rw [hab, hst']

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]

/-- A halting configuration is irreducible: no transition leaves the halting state. -/
theorem not_transitionRelation_haltCfg (tm : SingleTapeTM Symbol) (l : List Symbol)
    (y : tm.Cfg) : ¬ tm.TransitionRelation (tm.haltCfg l) y := by
  intro hy
  simp only [TransitionRelation, haltCfg, step] at hy
  exact absurd hy (by simp)

/-- The output list of a halting machine run is unique: the machine is deterministic. -/
theorem Outputs_unique (tm : SingleTapeTM Symbol) {l l₁ l₂ : List Symbol}
    (h1 : tm.Outputs l l₁) (h2 : tm.Outputs l l₂) : l₁ = l₂ := by
  have hcfg : tm.haltCfg l₁ = tm.haltCfg l₂ := by
    refine Relation.ReflTransGen.unique_of_deterministic (R := tm.TransitionRelation)
      (fun {a b c} hab hac => ?_) h1 h2 (not_transitionRelation_haltCfg tm l₁)
      (not_transitionRelation_haltCfg tm l₂)
    rw [TransitionRelation] at hab hac
    rw [hab] at hac
    exact Option.some.inj hac
  have := congrArg Cfg.BiTape hcfg
  simp only [haltCfg] at this
  exact Cslib.Turing.BiTape.mk₁_injective this

/-- A polynomial-time machine halts with the correct output on every input. -/
theorem PolyTimeComputable.outputs {f : List Symbol → List Symbol}
    (h : PolyTimeComputable f) (a : List Symbol) : h.tm.Outputs a (f a) := by
  obtain ⟨m, _, hm⟩ := h.outputsFunInTime a
  exact hm.reflTransGen

end Determinism

/-! ## State normalization -/

/-- Every `SingleTapeTM Bool` computing a string function with at most `d` states computes
the same function as `reify` of some `TMTable d` — the state space is relabeled to `Fin d`
along `Fintype.equivFin`, preserving the `Outputs` relation. It is the machine-theoretic
input to `exists_realizableLE_covering`. -/
theorem exists_tmTable_of_card_le {f : List Bool → List Bool} (h : PolyTimeComputable f)
    {d : ℕ} (hd : Fintype.card h.tm.State ≤ d) :
    ∃ t : TMTable d, ∀ l l', (reify t).Outputs l l' ↔ h.tm.Outputs l l' := by
  set tm := h.tm with htm
  refine ⟨normTable tm (embFin hd) (decFin (α := tm.State)), fun l l' => ?_⟩
  have hdec : ∀ s, decFin (α := tm.State) (embFin hd s) = some s := decFin_embFin hd
  have hemb : Function.Injective (embFin (α := tm.State) hd) := embFin_injective hd
  have hinit : normCfg tm (embFin hd) (decFin (α := tm.State)) (tm.initCfg l)
      = (reify (normTable tm (embFin hd) (decFin (α := tm.State)))).initCfg l := rfl
  have hhalt : normCfg tm (embFin hd) (decFin (α := tm.State)) (tm.haltCfg l')
      = (reify (normTable tm (embFin hd) (decFin (α := tm.State)))).haltCfg l' := rfl
  constructor
  · intro hout
    have hout' : Relation.ReflTransGen
        (reify (normTable tm (embFin hd) (decFin (α := tm.State)))).TransitionRelation
        (normCfg tm (embFin hd) (decFin (α := tm.State)) (tm.initCfg l))
        ((reify (normTable tm (embFin hd) (decFin (α := tm.State)))).haltCfg l') := by
      rw [hinit]; exact hout
    obtain ⟨c₂, hc₂, hrun⟩ := reflTransGen_normCfg_reverse hdec hout'
    rw [← hhalt] at hc₂
    have hcfg : tm.haltCfg l' = c₂ := normCfg_injective hemb hc₂
    rw [← hcfg] at hrun
    exact hrun
  · intro hout
    have hmap := normCfg_reflTransGen hdec hout
    rw [hinit, hhalt] at hmap
    exact hmap

end Cslib.Turing.SingleTapeTM

namespace Computability

open Cslib.Turing.SingleTapeTM

/-! ## Realizable predicates -/

/-- The predicates `BitVec n → Bool` realizable at description size at most `d`: those
computed by an initialization witness into some state encoding followed by an output
witness, both `EncPolyTime` machines of description size at most `d`, against the canonical
`BitVec`/`Option Bool` boundary encodings. An implementing machine adversary at these
boundaries lands its computed predicate here (its `initF`/`outputF` witnesses), and the
count of such predicates is controlled by counting the underlying machines
(`exists_realizableLE_covering`). -/
def RealizableLE (n d : ℕ) : Set (BitVec n → Bool) :=
  {g | ∃ (σ : Type) (es : σ → List Bool) (init : BitVec n → σ) (output : σ → Option Bool)
        (_i : EncPolyTime (BitEncFam.bitVecX.enc n) es init)
        (_o : EncPolyTime es (BitEncFam.bool.option.enc n) output),
      _i.size ≤ d ∧ _o.size ≤ d ∧ ∀ x, output (init x) = some (g x)}

/-- Realizability at a larger description size is a weaker requirement. -/
theorem realizableLE_mono {n : ℕ} {d d' : ℕ} (h : d ≤ d') :
    RealizableLE n d ⊆ RealizableLE n d' := by
  rintro g ⟨σ, es, init, output, i, o, hi, ho, hg⟩
  exact ⟨σ, es, init, output, i, o, hi.trans h, ho.trans h, hg⟩

open Classical in
/-- The total predicate `BitVec n → Bool` attached to a pair of canonical `d`-state tables:
run `reify p.1` on the canonical input encoding of `x`, feed its (deterministic) output to
`reify p.2`, and decode the resulting canonical `Option Bool` encoding. Totality is ensured
by a deterministic choice over the (at most one, by `Outputs_unique`) successful run, with
an arbitrary `false` fallback where no such run exists — no claim that either raw table
pair halts or is polynomial-time. -/
noncomputable def tablePairPred (n d : ℕ) (p : TMTable d × TMTable d) : BitVec n → Bool :=
  fun x =>
    if h : ∃ b : Bool, ∃ l₁ : List Bool,
        (reify p.1).Outputs (BitEncFam.bitVecX.enc n x) l₁ ∧
        (reify p.2).Outputs l₁ (BitEncFam.bool.option.enc n (some b))
    then h.choose else false

/-- The realizable predicates at description size at most `d` are covered by a `Finset` of
cardinality at most `B d ^ 2`. State normalization (`exists_tmTable_of_card_le`) reduces each
realizing pair of witness machines to a pair `TMTable d × TMTable d` of canonical `d`-state
tables; the realized predicate is recovered from the two tables by `tablePairPred` (running
both reified machines and decoding the canonical output encoding, using determinism of the
runs via `Outputs_unique`). Thus `RealizableLE n d` lands in the image of
`TMTable d × TMTable d` under `tablePairPred`, whence
`card ≤ Fintype.card (TMTable d × TMTable d) = B d ^ 2` (`card_tmTable`). The map need not be
injective — it only needs to cover the realizable set. -/
theorem exists_realizableLE_covering (n d : ℕ) :
    ∃ s : Finset (BitVec n → Bool), RealizableLE n d ⊆ ↑s ∧ s.card ≤ B d ^ 2 := by
  classical
  refine ⟨Finset.image (tablePairPred n d)
    (Finset.univ : Finset (TMTable d × TMTable d)), ?_, ?_⟩
  · rintro g ⟨σ, es, init, output, i, o, hi, ho, hg⟩
    obtain ⟨t₁, ht₁⟩ := exists_tmTable_of_card_le i.polyTime (d := d) hi
    obtain ⟨t₂, ht₂⟩ := exists_tmTable_of_card_le o.polyTime (d := d) ho
    refine Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨(t₁, t₂), Finset.mem_univ _, ?_⟩)
    funext x
    have hrun1 : (reify t₁).Outputs (BitEncFam.bitVecX.enc n x) (es (init x)) := by
      rw [ht₁]
      have h := i.polyTime.outputs (BitEncFam.bitVecX.enc n x)
      rwa [i.map_encode x] at h
    have hrun2 : (reify t₂).Outputs (es (init x))
        (BitEncFam.bool.option.enc n (some (g x))) := by
      rw [ht₂]
      have h := o.polyTime.outputs (es (init x))
      rwa [o.map_encode (init x), hg x] at h
    have hex : ∃ b : Bool, ∃ l₁ : List Bool,
        (reify t₁).Outputs (BitEncFam.bitVecX.enc n x) l₁ ∧
        (reify t₂).Outputs l₁ (BitEncFam.bool.option.enc n (some b)) :=
      ⟨g x, es (init x), hrun1, hrun2⟩
    have hpick : tablePairPred n d (t₁, t₂) x = hex.choose := dif_pos hex
    rw [hpick]
    obtain ⟨l₁', hl1', hl2'⟩ := hex.choose_spec
    have hl1eq : l₁' = es (init x) := Outputs_unique _ hl1' hrun1
    rw [hl1eq] at hl2'
    have henc := Outputs_unique _ hl2' hrun2
    exact Option.some.inj ((BitEncFam.bool.option).enc_injective n henc)
  · refine Finset.card_image_le.trans ?_
    rw [Finset.card_univ, Fintype.card_prod, card_tmTable, sq]

/-! ## Cardinality of the predicate space -/

/-- There are exactly `2 ^ (2 ^ n)` predicates `BitVec n → Bool`. -/
theorem card_bitVec_fun (n : ℕ) : Fintype.card (BitVec n → Bool) = 2 ^ (2 ^ n) := by
  rw [Fintype.card_fun, Fintype.card_bool, ← FinEnum.card_eq_fintypeCard, FinEnum.card_bitVec]

/-! ## Polynomial versus exponential growth -/

/-- Any fixed power is eventually dominated by `2 ^ n`. -/
theorem nat_pow_le_two_pow (k : ℕ) : ∀ᶠ n in atTop, n ^ k ≤ 2 ^ n := by
  have h : (fun n : ℕ => (n : ℝ) ^ k) =o[atTop] fun n : ℕ => (2 : ℝ) ^ n :=
    isLittleO_pow_const_const_pow_of_one_lt k (by norm_num)
  refine h.eventuallyLE.mono fun n hn => ?_
  simp only [Real.norm_eq_abs] at hn
  rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)] at hn
  exact_mod_cast (by push_cast; exact hn : ((n ^ k : ℕ) : ℝ) ≤ ((2 ^ n : ℕ) : ℝ))

/-- A constant multiple of any fixed power of `n + 1` is eventually dominated by `2 ^ n`. -/
theorem const_mul_pow_le_two_pow (C k : ℕ) : ∀ᶠ m in atTop, C * (m + 1) ^ k ≤ 2 ^ m := by
  filter_upwards [eventually_ge_atTop (C * 2 ^ k), eventually_ge_atTop 1,
    nat_pow_le_two_pow (k + 1)] with m hm hm1 hm3
  calc C * (m + 1) ^ k ≤ C * (2 * m) ^ k :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) k)
    _ = C * 2 ^ k * m ^ k := by rw [mul_pow]; ring
    _ ≤ m * m ^ k := Nat.mul_le_mul_right _ hm
    _ = m ^ (k + 1) := by rw [pow_succ]; ring
    _ ≤ 2 ^ m := hm3

/-- **Polynomials are eventually dominated by `2 ^ (n / 4)`.** The exponent `n / 4` is the
threshold fed to the machine count: fast enough to eventually exceed every polynomial
description bound (this lemma), yet slow enough that the resulting machine count stays below
`2 ^ (2 ^ n)` (`eventually_count_lt`). -/
theorem eventually_poly_le (p : Polynomial ℕ) :
    ∀ᶠ n in atTop, p.eval n ≤ 2 ^ (n / 4) := by
  obtain ⟨C, k, hCk⟩ : ∃ C k : ℕ, ∀ n : ℕ, p.eval n ≤ C * (n + 1) ^ k := by
    refine ⟨∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i, p.natDegree, fun n => ?_⟩
    rw [Polynomial.eval_eq_sum_range, Finset.sum_mul]
    refine Finset.sum_le_sum fun i hi => ?_
    rw [Finset.mem_range] at hi
    exact Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left (by omega) i).trans
      (Nat.pow_le_pow_right (by omega) (by omega)))
  have htend : Tendsto (fun n : ℕ => n / 4) atTop atTop :=
    Nat.tendsto_div_const_atTop (by norm_num)
  filter_upwards [htend.eventually (const_mul_pow_le_two_pow (C * 4 ^ k) k)] with n hn
  calc p.eval n ≤ C * (n + 1) ^ k := hCk n
    _ ≤ C * 4 ^ k * (n / 4 + 1) ^ k := by
        rw [mul_assoc, ← mul_pow]
        exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) k)
    _ ≤ 2 ^ (n / 4) := hn

/-- A crude closed-form bound on the squared machine count: for `9 * (d + 1) ≤ 2 ^ d` and
`d ≥ 1`, `B d ^ 2 ≤ 2 ^ (8 * d ^ 2)`. Uses `9 * (d + 1) ≤ 2 ^ d` on the statement/next-state
base and `d ^ 2 ≤ 2 ^ (2 * d)` on the initial-state factor. -/
theorem B_sq_le (d : ℕ) (hd : 9 * (d + 1) ≤ 2 ^ d) (hd1 : 1 ≤ d) :
    B d ^ 2 ≤ 2 ^ (8 * d ^ 2) := by
  have hd2 : d ^ 2 ≤ 2 ^ (2 * d) := by
    calc d ^ 2 ≤ (2 ^ d) ^ 2 := Nat.pow_le_pow_left (Nat.le_of_lt d.lt_two_pow_self) 2
      _ = 2 ^ (2 * d) := by rw [← pow_mul, Nat.mul_comm]
  calc B d ^ 2 = ((9 * (d + 1)) ^ (3 * d)) ^ 2 * d ^ 2 := by rw [B, mul_pow]
    _ = (9 * (d + 1)) ^ (6 * d) * d ^ 2 := by rw [← pow_mul]; ring_nf
    _ ≤ (2 ^ d) ^ (6 * d) * 2 ^ (2 * d) := Nat.mul_le_mul (Nat.pow_le_pow_left hd _) hd2
    _ = 2 ^ (6 * d ^ 2) * 2 ^ (2 * d) := by rw [← pow_mul]; ring_nf
    _ = 2 ^ (6 * d ^ 2 + 2 * d) := by rw [← pow_add]
    _ ≤ 2 ^ (8 * d ^ 2) := Nat.pow_le_pow_right (by norm_num) (by nlinarith [hd1])

/-- **The squared machine count at the threshold size `2 ^ (n / 4)` stays below the
predicate count `2 ^ (2 ^ n)` eventually.** The count at size `d = 2 ^ (n / 4)` is at most
`2 ^ (8 * d ^ 2)` (`B_sq_le`, whose hypothesis `9 * (d + 1) ≤ 2 ^ d` holds cofinitely as
`d → ∞`), and its exponent `8 * d ^ 2 = 2 ^ (3 + n / 4 * 2)` is eventually below `2 ^ n`. -/
theorem eventually_count_lt :
    ∀ᶠ n in atTop, B (2 ^ (n / 4)) ^ 2 < 2 ^ (2 ^ n) := by
  have htwo : Tendsto (fun m : ℕ => 2 ^ m) atTop atTop :=
    tendsto_atTop_mono (fun m => (Nat.lt_two_pow_self).le) tendsto_id
  have htend : Tendsto (fun n : ℕ => 2 ^ (n / 4)) atTop atTop :=
    htwo.comp (Nat.tendsto_div_const_atTop (by norm_num))
  filter_upwards [htend.eventually (const_mul_pow_le_two_pow 9 1),
    eventually_ge_atTop 8] with n ha hn
  rw [pow_one] at ha
  refine lt_of_le_of_lt (B_sq_le _ ha Nat.one_le_two_pow) ?_
  apply Nat.pow_lt_pow_right (by norm_num)
  calc 8 * (2 ^ (n / 4)) ^ 2
      = 2 ^ (3 + n / 4 * 2) := by rw [show (8 : ℕ) = 2 ^ 3 from rfl, ← pow_mul, ← pow_add]
    _ < 2 ^ n := Nat.pow_lt_pow_right (by norm_num) (by omega)

/-! ## The diagonal predicate -/

/-- A `Finset` family of subexponential cardinality misses a predicate eventually: if
`(S n).card < 2 ^ (2 ^ n)` cofinitely, some family `f` has `f n ∉ S n` cofinitely. -/
theorem exists_diagonal (S : (n : ℕ) → Finset (BitVec n → Bool))
    (hS : ∀ᶠ n in atTop, (S n).card < 2 ^ (2 ^ n)) :
    ∃ f : (n : ℕ) → BitVec n → Bool, ∀ᶠ n in atTop, f n ∉ S n := by
  classical
  have key : ∀ n, (S n).card < 2 ^ (2 ^ n) → ∃ g : BitVec n → Bool, g ∉ S n := by
    intro n hn
    have hlt : (S n).card < (Finset.univ : Finset (BitVec n → Bool)).card := by
      rw [Finset.card_univ, card_bitVec_fun]; exact hn
    obtain ⟨e, -, he⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    exact ⟨e, he⟩
  refine ⟨fun n => if h : (S n).card < 2 ^ (2 ^ n) then (key n h).choose else default, ?_⟩
  refine hS.mono fun n hn => ?_
  simp only [dif_pos hn]
  exact (key n hn).choose_spec

end Computability
