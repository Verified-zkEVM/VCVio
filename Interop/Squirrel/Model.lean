/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Squirrel.Syntax
public import VCVio.OracleComp.Constructions.SampleableType.Basic

/-!
# Models of Squirrel's local terms, read at one point

A model of a declaration environment (LICS23 §II-A.2, §II-A.3, §II-B) gives, for each security
parameter `η`,

* each base type a nonempty set of bitstrings: a domain with its injective encoding;
* the attacker tape, a bitstring `ρa` of model-chosen length `lenA η` (`Model.TapeA`; LICS23
  §II-A.3 takes both tapes to be finite bitstrings "long enough" for the machines considered);
* for each type, the number of honest-tape bits a name of that type reads and a sampler mapping
  those bits to a value;
* each name a function of its index and the honest tape;
* each honest function symbol a value, and each attacker function symbol a function of the
  attacker tape.

`interp M η ρ` reads local syntax at the parameter `η` and the tapes `ρ = (ρa, ρh)`: booleans are
`Bool`, arrows are full function spaces, and `=_τ`, `∀_τ`, `∃_τ` have their intended meaning.
`Bool`, not `Prop`, interprets `bool`, because LICS23 interprets it as `{0, 1}` and a conditional
needs a decidable test. Equality and the quantifiers range over function spaces, so they decide
their propositions classically.

Names follow LICS23 §II-B.2 structurally: the honest tape is a product with one uniform bit block
per name and index, a name reads its own block and runs the sampler of its type on it, and names
of one type share a sampler. So samplings for distinct name-index pairs are independent and those
of one type are identically distributed; and a machine that reads the same number of bits from
its own tape and runs the sampler produces a name's distribution. That samplers run in
polynomial time is not a restriction here.

## Main results

* `denote_app_lam`: β-reduction is sound, from `Term.denote_substOne`;
* `denote_substOne_congr`: replacing a subterm by one with the same meaning preserves meaning,
  the semantic core of local rewriting (LICS23 Fig. 7, L.Rewrite);
* `denote_eq_app_of_eq`: function application is a congruence for local equality;
* `Ty.finite_value`, `Ty.value_eq_of_fixed`, `Model.isLarge_of_hasLabel`: what the labels give.

`Ty.appVals` applies a curried function of a tuple (`Ty.arrows`) to a vector of values,
`Ty.curryVals` is its inverse, and `Ty.postcomp` composes after it: the logic has no product
types, so attacker functions of tuples are curried. `Ty.apply` and `Ty.curry` do the same for the
argument spine `Ty.args` of a type, with result `Ty.res`: this is how a machine queries an input
of order at most one. The arguments of `τ₁ → … → τₙ → ρ` split into those of the tuple and those
of `ρ` (`Ty.splitArgs`), which is how a machine answers a query to an attacker function of a tuple
(`Ty.apply_curryVals_curry`). Equality of values of a Boolean or base type is decidable
(`Ty.decEqValue`), which is how a machine tests it.

## References

* [LICS23] Baelde, Koutsos, Lallemand, *A Higher-Order Indistinguishability Logic for
  Cryptographic Reasoning*, LICS 2023: §II-A, §II-B, Fig. 7 and App. A.
* [CSF24] Baelde, Fontaine, Koutsos, Scerri, Vignon, *A Probabilistic Logic for Concrete
  Security*, CSF 2024: App. A.
* [CCS26] Hérouard, Jacomme, Koutsos, Lallemand, *Secrecy in Squirrel and the Post-Compromise
  Security of a Ratchet*, CCS 2026: §3.1.
-/

public section

namespace Interop.Squirrel

open IPFunctor IPFunctor.ScopedSignature

variable {B : Type}

/-- The meaning of a type at `η`, given the carriers of the base types. -/
@[expose, reducible] def Ty.Value (carrier : B → ℕ → Set (List Bool)) (η : ℕ) : Ty B → Type
  | .bool => Bool
  | .base b => carrier b η
  | .arrow a b => a.Value carrier η → b.Value carrier η

/-- A curried function of the tuple `τs` applied to a vector of arguments. -/
@[expose] def Ty.appVals {carrier : B → ℕ → Set (List Bool)} {η : ℕ} {β : Ty B} :
    {τs : List (Ty B)} → (Ty.arrows τs β).Value carrier η → Env (Ty.Value carrier η) τs →
      β.Value carrier η
  | [], g, _ => g
  | _ :: _, g, e => Ty.appVals (g (e _ .zero)) fun _ x => e _ (.succ x)

@[simp] theorem Ty.appVals_nil {carrier : B → ℕ → Set (List Bool)} {η : ℕ} {β : Ty B}
    (g : (Ty.arrows [] β).Value carrier η) (e : Env (Ty.Value carrier η) []) :
    Ty.appVals g e = g := rfl

@[simp] theorem Ty.appVals_cons {carrier : B → ℕ → Set (List Bool)} {η : ℕ} {β τ : Ty B}
    {τs : List (Ty B)} (g : (Ty.arrows (τ :: τs) β).Value carrier η) (x : τ.Value carrier η)
    (e : Env (Ty.Value carrier η) τs) : Ty.appVals g (Env.cons x e) = Ty.appVals (g x) e := rfl

/-- Post-composition of a curried function of the tuple `τs` with `k`. -/
@[expose] def Ty.postcomp {carrier : B → ℕ → Set (List Bool)} {η : ℕ} {β γ : Ty B}
    (k : β.Value carrier η → γ.Value carrier η) :
    {τs : List (Ty B)} → (Ty.arrows τs β).Value carrier η → (Ty.arrows τs γ).Value carrier η
  | [], g => k g
  | _ :: _, g => fun x => Ty.postcomp k (g x)

@[simp] theorem Ty.appVals_postcomp {carrier : B → ℕ → Set (List Bool)} {η : ℕ} {β γ : Ty B}
    (k : β.Value carrier η → γ.Value carrier η) :
    ∀ {τs : List (Ty B)} (g : (Ty.arrows τs β).Value carrier η) (e : Env (Ty.Value carrier η) τs),
      Ty.appVals (Ty.postcomp k g) e = k (Ty.appVals g e)
  | [], _, _ => rfl
  | _ :: _, g, e => Ty.appVals_postcomp k (g (e _ .zero)) _

/-- A curried function of the tuple `τs`, from a function of a vector of arguments: the inverse
of `Ty.appVals`. -/
@[expose] def Ty.curryVals {carrier : B → ℕ → Set (List Bool)} {η : ℕ} {β : Ty B} :
    {τs : List (Ty B)} → (Env (Ty.Value carrier η) τs → β.Value carrier η) →
      (Ty.arrows τs β).Value carrier η
  | [], g => g Env.empty
  | _ :: _, g => fun x => Ty.curryVals fun e => g (Env.cons x e)

@[simp] theorem Ty.appVals_curryVals {carrier : B → ℕ → Set (List Bool)} {η : ℕ} {β : Ty B} :
    ∀ {τs : List (Ty B)} (g : Env (Ty.Value carrier η) τs → β.Value carrier η)
      (e : Env (Ty.Value carrier η) τs), Ty.appVals (Ty.curryVals g) e = g e
  | [], g, e => by rw [Env.eq_empty e]; rfl
  | _ :: _, g, e => by
    rw [← Env.cons_eta e, Ty.appVals_cons]
    exact Ty.appVals_curryVals (fun e' => g (Env.cons _ e')) _

theorem Ty.postcomp_curryVals {carrier : B → ℕ → Set (List Bool)} {η : ℕ} {β γ : Ty B}
    (k : β.Value carrier η → γ.Value carrier η) :
    ∀ {τs : List (Ty B)} (g : Env (Ty.Value carrier η) τs → β.Value carrier η),
      Ty.postcomp k (Ty.curryVals g) = Ty.curryVals (k ∘ g)
  | [], _ => rfl
  | _ :: _, g => funext fun x => Ty.postcomp_curryVals k fun e => g (Env.cons x e)

/-! ## Argument spines

A value of `τ = a₁ → … → aₖ → b`, with `b` a Boolean or base type, is used by applying it to all
its arguments: `Ty.args τ = [a₁, …, aₖ]` and `Ty.res τ = b`. A machine queries an input of type
`τ` with a vector of `Ty.args τ` and receives a value of `Ty.res τ` (LICS23 §II-C.1, the query
tape). `τ` has order at most one when its arguments are Booleans or base types (`Ty.order`). -/

/-- The argument types of `τ`. -/
@[expose] def Ty.args : Ty B → List (Ty B)
  | .arrow a b => a :: b.args
  | _ => []

/-- The type of `τ` applied to all its arguments: a Boolean or base type. -/
@[expose] def Ty.res : Ty B → Ty B
  | .arrow _ b => b.res
  | τ => τ

/-- The order of a type: Booleans and base types have order zero, and `a → b` has order
`max (order a + 1) (order b)`. -/
@[expose] def Ty.order : Ty B → ℕ
  | .arrow a b => max (a.order + 1) b.order
  | _ => 0

/-- Types of order zero are the Boolean and base types. -/
theorem Ty.isGround_iff_order_eq_zero : ∀ {τ : Ty B}, τ.IsGround ↔ τ.order = 0
  | .bool => iff_of_true trivial rfl
  | .base _ => iff_of_true trivial rfl
  | .arrow _ _ => iff_of_false id (by simp [Ty.order])

theorem Ty.isGround_bool : (Ty.bool : Ty B).IsGround := trivial

theorem Ty.isGround_base (b : B) : (Ty.base b).IsGround := trivial

/-- The argument of a function of order at most one is a Boolean or base type. -/
theorem Ty.isGround_of_order_arrow_le_one {a b : Ty B} (h : (Ty.arrow a b).order ≤ 1) :
    a.IsGround :=
  Ty.isGround_iff_order_eq_zero.2 (by simp only [Ty.order] at h; omega)

/-- The arguments of a type of order at most one are Boolean or base types. -/
theorem Ty.isGround_of_mem_args : ∀ {τ : Ty B}, τ.order ≤ 1 → ∀ σ ∈ τ.args, σ.IsGround
  | .bool, _, _, h => absurd h List.not_mem_nil
  | .base _, _, _, h => absurd h List.not_mem_nil
  | .arrow a b, hτ, σ, hσ => by
    rcases List.mem_cons.1 hσ with rfl | hσ
    · exact Ty.isGround_of_order_arrow_le_one hτ
    · exact Ty.isGround_of_mem_args (le_trans (le_max_right _ _) hτ) σ hσ

section Spine

/-- The entries of `u⃗ ∼ v⃗` have order at most one (CSF24 App. A; CCS26 §3.1, p. 6). -/
@[expose, reducible] def Ty.IndistOrder (τs : List (Ty B)) : Prop := ∀ τ ∈ τs, τ.order ≤ 1

instance (τs : List (Ty B)) : Decidable (Ty.IndistOrder τs) :=
  inferInstanceAs (Decidable (∀ τ ∈ τs, τ.order ≤ 1))

/-- `adv` applies to terms of order at most two (CSF24 App. A; CCS26 §3.1, p. 6): here, to a term
of type `τ₁ → … → τₙ → β`. -/
@[expose, reducible] def Ty.AdvOrder (τs : List (Ty B)) (β : Ty B) : Prop :=
  (Ty.arrows τs β).order ≤ 2

instance (τs : List (Ty B)) (β : Ty B) : Decidable (Ty.AdvOrder τs β) :=
  inferInstanceAs (Decidable ((Ty.arrows τs β).order ≤ 2))

/-- `u⃗ ⊬ v` and `u⃗ ▷ v` relate terms of order at most one, so that their attacker functions have
order at most two (CCS26 §3.1, p. 6). -/
@[expose, reducible] def Ty.SecrecyOrder (τs : List (Ty B)) (β : Ty B) : Prop :=
  Ty.IndistOrder τs ∧ β.order ≤ 1

instance (τs : List (Ty B)) (β : Ty B) : Decidable (Ty.SecrecyOrder τs β) :=
  inferInstanceAs (Decidable (Ty.IndistOrder τs ∧ β.order ≤ 1))

namespace Ty.IndistOrder

variable {τ : Ty B} {τs τs' : List (Ty B)}

theorem head (h : Ty.IndistOrder (τ :: τs)) : τ.order ≤ 1 := h τ List.mem_cons_self

theorem tail (h : Ty.IndistOrder (τ :: τs)) : Ty.IndistOrder τs :=
  fun σ hσ => h σ (List.mem_cons_of_mem _ hσ)

theorem cons (hτ : τ.order ≤ 1) (h : Ty.IndistOrder τs) : Ty.IndistOrder (τ :: τs) :=
  List.forall_mem_cons.2 ⟨hτ, h⟩

theorem append_left (h : Ty.IndistOrder (τs ++ τs')) : Ty.IndistOrder τs :=
  fun σ hσ => h σ (List.mem_append_left _ hσ)

theorem append_right (h : Ty.IndistOrder (τs ++ τs')) : Ty.IndistOrder τs' :=
  fun σ hσ => h σ (List.mem_append_right _ hσ)

theorem append (h : Ty.IndistOrder τs) (h' : Ty.IndistOrder τs') :
    Ty.IndistOrder (τs ++ τs') :=
  fun σ hσ => (List.mem_append.1 hσ).elim (h σ) (h' σ)

theorem rename (r : Renaming τs' τs) (h : Ty.IndistOrder τs) : Ty.IndistOrder τs' :=
  fun σ hσ => (nonempty_scopedVar_iff.2 hσ).elim fun x => h σ (r σ x).mem

theorem dup (h : Ty.IndistOrder (τ :: τs)) : Ty.IndistOrder (τ :: τ :: τs) := h.cons h.head

theorem single (h : τ.order ≤ 1) : Ty.IndistOrder [τ] :=
  Ty.IndistOrder.cons h fun _ hσ => absurd hσ List.not_mem_nil

theorem ite {a : Ty B} (h : Ty.IndistOrder (.bool :: a :: a :: τs)) : Ty.IndistOrder (a :: τs) :=
  h.tail.tail.tail.cons h.tail.head

theorem app {a b : Ty B} (h : Ty.IndistOrder (.arrow a b :: a :: τs)) :
    Ty.IndistOrder (b :: τs) :=
  h.tail.tail.cons (le_trans (le_max_right _ _) h.head)

/-- The argument of the first entry of FA-App is a Boolean or base type. -/
theorem isGround_app {a b : Ty B} (h : Ty.IndistOrder (.arrow a b :: a :: τs)) : a.IsGround :=
  Ty.isGround_of_order_arrow_le_one h.head

end Ty.IndistOrder

theorem Ty.order_cod_le (a b : Ty B) : b.order ≤ (Ty.arrow a b).order := le_max_right _ _

/-- The attacker functions of `⊬` and `▷` have order at most two. -/
theorem Ty.SecrecyOrder.advOrder :
    ∀ {τs : List (Ty B)} {β : Ty B}, Ty.SecrecyOrder τs β → Ty.AdvOrder τs β
  | [], _, h => le_trans h.2 (by norm_num)
  | _ :: _, _, h => by
    have ih := Ty.SecrecyOrder.advOrder ⟨h.1.tail, h.2⟩
    have hd := h.1.head
    simp only [Ty.AdvOrder, Ty.arrows, Ty.order] at ih ⊢
    omega

variable {carrier : B → ℕ → Set (List Bool)} {η : ℕ}

/-- Apply a value of `τ` to all its arguments. -/
@[expose] def Ty.apply : {τ : Ty B} → τ.Value carrier η → Env (Ty.Value carrier η) τ.args →
    τ.res.Value carrier η
  | .bool, v, _ => v
  | .base _, v, _ => v
  | .arrow _ b, f, q => Ty.apply (τ := b) (f (q _ .zero)) fun _ x => q _ (.succ x)

/-- The value of `τ` whose application to every argument vector is `g`: the inverse of
`Ty.apply`. -/
@[expose] def Ty.curry : {τ : Ty B} → (Env (Ty.Value carrier η) τ.args → τ.res.Value carrier η) →
    τ.Value carrier η
  | .bool, g => g Env.empty
  | .base _, g => g Env.empty
  | .arrow _ b, g => fun x => Ty.curry (τ := b) fun q => g (Env.cons x q)

@[simp] theorem Ty.apply_curry : ∀ {τ : Ty B}
    (g : Env (Ty.Value carrier η) τ.args → τ.res.Value carrier η) (q : Env _ τ.args),
    Ty.apply (Ty.curry g) q = g q
  | .bool, g, q => by rw [Env.eq_empty q]; rfl
  | .base _, g, q => by rw [Env.eq_empty q]; rfl
  | .arrow a b, g, q =>
    (Ty.apply_curry (τ := b) (fun q' => g (Env.cons (q _ .zero) q')) _).trans
      (congrArg g (Env.cons_eta (Γ := b.args) (a := a) q))

@[simp] theorem Ty.curry_apply : ∀ {τ : Ty B} (v : τ.Value carrier η),
    Ty.curry (Ty.apply v) = v
  | .bool, _ => rfl
  | .base _, _ => rfl
  | .arrow _ b, f => funext fun x => by
    change Ty.curry (τ := b) (fun q => Ty.apply (f x) q) = f x
    exact Ty.curry_apply (f x)

/-- The arguments of a Boolean or base type: none. -/
@[expose] def Ty.groundArgs : {τ : Ty B} → τ.IsGround → Env (Ty.Value carrier η) τ.args
  | .bool, _ => Env.empty
  | .base _, _ => Env.empty
  | .arrow _ _, h => h.elim

/-- A Boolean or base type is its own result type. -/
@[expose] def Ty.ofRes : {τ : Ty B} → τ.IsGround → τ.res.Value carrier η → τ.Value carrier η
  | .bool, _, v => v
  | .base _, _, v => v
  | .arrow _ _, h, _ => h.elim

@[simp] theorem Ty.ofRes_apply_groundArgs : ∀ {τ : Ty B} (h : τ.IsGround) (v : τ.Value carrier η),
    Ty.ofRes h (Ty.apply v (Ty.groundArgs h)) = v
  | .bool, _, _ => rfl
  | .base _, _, _ => rfl
  | .arrow _ _, h, _ => h.elim

/-- Equality of values of a Boolean or base type is decidable: they are Booleans or bitstrings. -/
@[expose, instance_reducible] def Ty.decEqValue :
    {τ : Ty B} → τ.IsGround → DecidableEq (τ.Value carrier η)
  | .bool, _ => inferInstanceAs (DecidableEq Bool)
  | .base b, _ => inferInstanceAs (DecidableEq (carrier b η))
  | .arrow _ _, h => h.elim

/-- The arguments of `τ₁ → … → τₙ → ρ`, split into those of the tuple and those of `ρ`. -/
@[expose] def Ty.splitArgs {ρ : Ty B} : (as : List (Ty B)) →
    Env (Ty.Value carrier η) (Ty.arrows as ρ).args →
      Env (Ty.Value carrier η) as × Env (Ty.Value carrier η) ρ.args
  | [], q => (Env.empty, q)
  | _ :: as, q =>
    let r := Ty.splitArgs as fun _ x => q _ (.succ x)
    (Env.cons (q _ .zero) r.1, r.2)

/-- `τ₁ → … → τₙ → ρ` and `ρ` have the same result type. -/
@[expose] def Ty.resArrows {ρ : Ty B} : (as : List (Ty B)) → ρ.res.Value carrier η →
    (Ty.arrows as ρ).res.Value carrier η
  | [], v => v
  | _ :: as, v => Ty.resArrows as v

/-- Applying a curried function of the tuple `as` and of `ρ`'s arguments to the arguments of
`τ₁ → … → τₙ → ρ` applies it to the two parts of the split. -/
theorem Ty.apply_curryVals_curry {ρ : Ty B} : ∀ (as : List (Ty B))
    (F : Env (Ty.Value carrier η) as → Env (Ty.Value carrier η) ρ.args → ρ.res.Value carrier η)
    (q : Env (Ty.Value carrier η) (Ty.arrows as ρ).args),
    Ty.apply (Ty.curryVals (β := ρ) fun a => Ty.curry (F a)) q =
      Ty.resArrows as (F (Ty.splitArgs as q).1 (Ty.splitArgs as q).2)
  | [], F, q => Ty.apply_curry (F Env.empty) q
  | _ :: as, F, q =>
    Ty.apply_curryVals_curry as (fun a => F (Env.cons (q _ .zero) a)) fun _ x => q _ (.succ x)

end Spine

/-- Random tapes: finite, nonempty sets for the attacker and for honest samplings. The uniform
distribution on them is VCVio's `$ᵗ`. -/
structure TapeModel where
  /-- The attacker's random tapes. -/
  TapeA : ℕ → Type
  /-- The honest random tapes, read by names. -/
  TapeH : ℕ → Type
  /-- Attacker tapes are finite and nonempty, with their uniform sampler. -/
  [sampleableA : ∀ η, SampleableType (TapeA η)]
  /-- Honest tapes are finite and nonempty, with their uniform sampler. -/
  [sampleableH : ∀ η, SampleableType (TapeH η)]

attribute [instance] TapeModel.sampleableA TapeModel.sampleableH

/-- Both tapes. -/
abbrev TapeModel.Tape (T : TapeModel) (η : ℕ) : Type := T.TapeA η × T.TapeH η

/-- A model of a declaration environment (LICS23 §II-A.3, §II-B). The tapes are bitstrings, as in
LICS23: the attacker tape `ρa` has a model-chosen length `lenA η`, and the honest tape is not a
field but the product of one bit block per name and index (`Model.TapeH`), which the name reads
and passes to the sampler of its type. -/
structure Model (D : Decl B) where
  /-- The length of the attacker tape at `η`. -/
  lenA : ℕ → ℕ
  /-- Each base type is a nonempty set of bitstrings at each `η`. -/
  carrier : B → ℕ → Set (List Bool)
  /-- Carriers are nonempty. -/
  nonempty : ∀ b η, (carrier b η).Nonempty
  /-- The number of honest-tape bits that a name of type `b` reads. -/
  coinLen : ℕ → Ty B → ℕ
  /-- The sampler for names of type `b`, run on the name's bits: names of one type follow one
  distribution. -/
  sample : ∀ η (b : Ty B), (Fin (coinLen η b) → Bool) → b.Value carrier η
  /-- Name indices are finite in the model. -/
  finite_index : ∀ η {a b : Ty B}, D.Name a b → Finite (a.Value carrier η)
  /-- An honest function symbol is a fixed value at each `η`. -/
  fn : ∀ η {τ : Ty B}, D.Fn τ → τ.Value carrier η
  /-- An attacker function symbol is computed from the attacker tape. -/
  att : ∀ η (f : D.Att), (Fin (lenA η) → Bool) → (D.attTy f).Value carrier η

variable {D : Decl B}

/-- The attacker tape at `η`: a bitstring of length `lenA η` (LICS23 §II-A.3). -/
abbrev Model.TapeA (M : Model D) (η : ℕ) : Type := Fin (M.lenA η) → Bool

/-- The bit block that a name of type `τ` reads at `η`. -/
abbrev Model.Coin (M : Model D) (η : ℕ) (τ : Ty B) : Type := Fin (M.coinLen η τ) → Bool

/-- Bit `i` of the attacker tape; past its end, `false`. -/
@[expose] def Model.readBit (M : Model D) {η : ℕ} (ρa : M.TapeA η) (i : ℕ) : Bool :=
  if h : i < M.lenA η then ρa ⟨i, h⟩ else false

/-- The coordinates of the honest tape at `η`: a name with its types, and an index. -/
abbrev Model.Slot (M : Model D) (η : ℕ) : Type :=
  (n : (a : Ty B) × (b : Ty B) × D.Name a b) × n.1.Value M.carrier η

/-- The honest tape at `η`: an independent bit block for every name and index (LICS23 §II-B.2).
It is reducible, so that lemmas about uniform dependent products, such as
`SampleableType.prEvent_uniformSample_prod_update_update`, apply to it and rewriting inside them
stays type-correct. -/
@[expose, reducible] def Model.TapeH (M : Model D) (η : ℕ) : Type :=
  (k : M.Slot η) → M.Coin η k.1.2.1

/-- The honest tape is uniform: its coordinates are independent uniform coins. -/
noncomputable instance Model.instSampleableTapeH (M : Model D) (η : ℕ) :
    SampleableType (M.TapeH η) :=
  haveI := D.finite_names
  haveI : ∀ n : (a : Ty B) × (b : Ty B) × D.Name a b, Finite (n.1.Value M.carrier η) :=
    fun n => M.finite_index η n.2.2
  haveI := Fintype.ofFinite (M.Slot η)
  haveI : ∀ k : M.Slot η, Fintype (M.Coin η k.1.2.1) := fun _ => Fintype.ofFinite _
  SampleableType.piOfFintype _

/-- Both tapes. -/
abbrev Model.Tape (M : Model D) (η : ℕ) : Type := M.TapeA η × M.TapeH η

/-- The tapes of a model. -/
@[expose, reducible] noncomputable def Model.toTapeModel (M : Model D) : TapeModel where
  TapeA := M.TapeA
  TapeH := M.TapeH

/-- The coordinate of the honest tape that the name `n` reads at `η` at the value of the honest
symbol `i`, a closed index. -/
abbrev Model.nameSlot (M : Model D) {a b : Ty B} (n : D.Name a b) (i : D.Fn a) (η : ℕ) :
    M.Slot η :=
  ⟨⟨a, b, n⟩, M.fn η i⟩

/-- A name reads the coin of its own slot and runs the sampler of its type. -/
@[expose] def Model.name (M : Model D) (η : ℕ) {a b : Ty B} (n : D.Name a b)
    (i : a.Value M.carrier η) (ρh : M.TapeH η) : b.Value M.carrier η :=
  M.sample η b (ρh ⟨⟨a, b, n⟩, i⟩)

/-! ## Labels -/

/-- The sampler of names of type `τ` draws any one value with probability at most `2^{-cη}`, for
one `c > 0` and every `η`: LICS23's label `large` (App. A), which bounds
`Pr_ρh[⟦n⟧(η, a)(ρh) = b]` for every name `n` of type `τ`. Names of one type share their sampler,
so the bound is on the sampler. -/
@[expose] def Model.IsLarge (M : Model D) (τ : Ty B) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ η (y : τ.Value M.carrier η),
    Pr{let r ← $ᵗ (M.Coin η τ)}[M.sample η τ r = y] ≤ (2 : ENNReal) ^ (-(c * η))

/-- What a label requires of a base type in a model (LICS23 App. A). -/
@[expose] def Label.Holds (M : Model D) (b : B) : Label → Prop
  | .finite => ∀ η, (M.carrier b η).Finite
  | .fixed => ∀ η η', M.carrier b η = M.carrier b η'
  | .large => M.IsLarge (.base b)

/-- A model respects the labels declared for its base types. -/
@[expose] def Model.RespectsLabels (M : Model D) : Prop :=
  ∀ b l, D.labels b l → l.Holds M b

/-- A type labelled `large` has a large sampler in every model respecting the labels; it is a base
type. -/
theorem Model.isLarge_of_hasLabel (M : Model D) (hM : M.RespectsLabels) :
    ∀ {τ : Ty B}, τ.HasLabel D.labels .large → M.IsLarge τ
  | .bool, h => absurd rfl h
  | .base b, h => hM b .large h
  | .arrow _ _, h => absurd rfl h.1

/-- Every type is finite when the carriers are finite. -/
theorem Ty.finite_value_of_finite {carrier : B → ℕ → Set (List Bool)}
    (h : ∀ b η, (carrier b η).Finite) (η : ℕ) : ∀ τ : Ty B, Finite (τ.Value carrier η)
  | .bool => inferInstanceAs (Finite Bool)
  | .base b => (h b η).to_subtype
  | .arrow a b =>
    have := a.finite_value_of_finite h η
    have := b.finite_value_of_finite h η
    inferInstanceAs (Finite (a.Value carrier η → b.Value carrier η))

/-- Every type is inhabited when the carriers are nonempty. -/
theorem Ty.nonempty_value {carrier : B → ℕ → Set (List Bool)}
    (h : ∀ b η, (carrier b η).Nonempty) (η : ℕ) : ∀ τ : Ty B, Nonempty (τ.Value carrier η)
  | .bool => ⟨true⟩
  | .base b => (h b η).to_subtype
  | .arrow _ b => ⟨fun _ => Classical.choice (b.nonempty_value h η)⟩

/-- A finite type is finite in every model respecting the labels. -/
theorem Ty.finite_value (M : Model D) (hM : M.RespectsLabels) (η : ℕ) :
    ∀ τ : Ty B, τ.HasLabel D.labels .finite → Finite (τ.Value M.carrier η)
  | .bool, _ => inferInstanceAs (Finite Bool)
  | .base b, h => (hM b .finite h η).to_subtype
  | .arrow a b, ⟨_, ha, hb⟩ =>
    have := a.finite_value M hM η ha
    have := b.finite_value M hM η hb
    inferInstanceAs (Finite (a.Value M.carrier η → b.Value M.carrier η))

/-- A fixed type has the same meaning at every security parameter. -/
theorem Ty.value_eq_of_fixed (M : Model D) (hM : M.RespectsLabels) (η η' : ℕ) :
    ∀ τ : Ty B, τ.HasLabel D.labels .fixed → τ.Value M.carrier η = τ.Value M.carrier η'
  | .bool, _ => rfl
  | .base b, h => congrArg (fun s : Set (List Bool) => (s : Type)) (hM b .fixed h η η')
  | .arrow a b, ⟨_, ha, hb⟩ => by
    simp only [Ty.Value, a.value_eq_of_fixed M hM η η' ha, b.value_eq_of_fixed M hM η η' hb]

/-! ## The pointwise reading -/

/-- The meaning of a sort at `η`: local types by `Ty.Value`; the global sort is not read
pointwise. -/
@[expose, reducible] def Kind.PtValue (M : Model D) (η : ℕ) : Kind B → Type
  | .loc τ => τ.Value M.carrier η
  | .glob => PUnit

/-- Local syntax read at the security parameter `η` and the tapes `ρ = (ρa, ρh)`: names read
`ρh`, attacker symbols read `ρa`. -/
@[expose] noncomputable def interp (M : Model D) (η : ℕ) (ρ : M.Tape η) :
    Interpretation (localSig D) (Kind.PtValue M η)
  | _, .app _ _, next => next 0 Env.empty (next 1 Env.empty)
  | _, .lam _ _, next => fun x => next 0 (Env.single x)
  | _, .ite _, next => cond (next 0 Env.empty) (next 1 Env.empty) (next 2 Env.empty)
  | _, .tt, _ => true
  | _, .ff, _ => false
  | _, .eq _, _ => fun x y => @decide (x = y) (Classical.propDecidable _)
  | _, .all _, _ => fun f => @decide (∀ x, f x = true) (Classical.propDecidable _)
  | _, .ex _, _ => fun f => @decide (∃ x, f x = true) (Classical.propDecidable _)
  | _, .name n, _ => fun i => M.name η n i ρ.2
  | _, .fn f, _ => M.fn η f
  | _, .att f, _ => M.att η f ρ.1

namespace LTerm

variable {M : Model D} {η : ℕ} {ρ : M.Tape η} {Γ : List (Kind B)} {a b : Ty B}
  {env : Env (Kind.PtValue M η) Γ}

@[simp] theorem denote_app (f : LTerm D Γ (.arrow a b)) (x : LTerm D Γ a) :
    (app f x).denote (interp M η ρ) env =
      f.denote (interp M η ρ) env (x.denote (interp M η ρ) env) := rfl

@[simp] theorem denote_lam (body : LTerm D (.loc a :: Γ) b) :
    (lam body).denote (interp M η ρ) env =
      fun x => body.denote (interp M η ρ) (Env.cons x env) := rfl

@[simp] theorem denote_ite (c : LTerm D Γ .bool) (t e : LTerm D Γ a) :
    (ite c t e).denote (interp M η ρ) env =
      cond (c.denote (interp M η ρ) env) (t.denote (interp M η ρ) env)
        (e.denote (interp M η ρ) env) := rfl

@[simp] theorem denote_tt : (tt : LTerm D Γ .bool).denote (interp M η ρ) env = true := rfl

@[simp] theorem denote_ff : (ff : LTerm D Γ .bool).denote (interp M η ρ) env = false := rfl

/-- `=_τ` means equality (LICS23 §II-B). -/
@[simp] theorem denote_eq_eq_true {t u : LTerm D Γ a} :
    (eq t u).denote (interp M η ρ) env = true ↔
      t.denote (interp M η ρ) env = u.denote (interp M η ρ) env :=
  @decide_eq_true_iff _ (Classical.propDecidable _)

/-- `∀_τ` means universal quantification over the whole carrier (LICS23 §II-B). -/
@[simp] theorem denote_all_eq_true {φ : LTerm D (.loc a :: Γ) .bool} :
    (all φ).denote (interp M η ρ) env = true ↔
      ∀ x, φ.denote (interp M η ρ) (Env.cons x env) = true :=
  @decide_eq_true_iff _ (Classical.propDecidable _)

/-! ## β-reduction and congruence -/

/-- **β.** A redex means its contraction, by `Term.denote_substOne`. -/
theorem denote_app_lam (body : LTerm D (.loc a :: Γ) b) (v : LTerm D Γ a) :
    (app (lam body) v).denote (interp M η ρ) env =
      (body.substOne v).denote (interp M η ρ) env := by
  rw [Term.denote_substOne, denote_app, denote_lam]

/-- Replacing a subterm by one with the same meaning preserves meaning, in any interpretation:
the semantic core of local rewriting (LICS23 Fig. 7, L.Rewrite). The context `C` is a term with
its hole as the nearest variable, so the replacement is capture-avoiding. -/
theorem denote_substOne_congr {V : Kind B → Type} (alg : Interpretation (localSig D) V)
    {s : Kind B} (C : (localSig D).Term (.loc a :: Γ) s) {t u : LTerm D Γ a}
    (ρ' : Env V Γ) (h : t.denote alg ρ' = u.denote alg ρ') :
    (C.substOne t).denote alg ρ' = (C.substOne u).denote alg ρ' := by
  rw [Term.denote_substOne, Term.denote_substOne, h]

/-- Local rewriting: where `s = t` holds, a formula about `s` means the same about `t`. -/
theorem denote_substOne_of_eq {s : Kind B} (C : (localSig D).Term (.loc a :: Γ) s)
    {t u : LTerm D Γ a} (h : (eq t u).denote (interp M η ρ) env = true) :
    (C.substOne t).denote (interp M η ρ) env = (C.substOne u).denote (interp M η ρ) env :=
  denote_substOne_congr _ C env (denote_eq_eq_true.1 h)

/-- **FA congruence.** Application preserves local equality. -/
theorem denote_eq_app_of_eq {f g : LTerm D Γ (.arrow a b)} {t u : LTerm D Γ a}
    (hf : (eq f g).denote (interp M η ρ) env = true)
    (ht : (eq t u).denote (interp M η ρ) env = true) :
    (eq (app f t) (app g u)).denote (interp M η ρ) env = true := by
  rw [denote_eq_eq_true] at hf ht ⊢
  rw [denote_app, denote_app, hf, ht]

end LTerm

end Interop.Squirrel
