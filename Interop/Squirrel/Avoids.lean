/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Squirrel.Global
public import PolyFun.IPFunctor.Scoped.Measure

/-!
# Terms that do not use some names

The honest tape is a product with one coin per name and index (`Model.TapeH`), and a name reads
only the coins of its own slots. So freshness of names is a syntactic condition: a term in which
no constructor is a name of a set `N` reads no coordinate of the honest tape that belongs to a name
in `N`. The condition is stated on PolyFun's heads of the term (`Term.heads`), the set of the
constructors it uses, with no induction over terms:

* `headName h` is the name the head `h` constructs, if it is a name, and `AvoidsNamesAt N h` says
  that it is not a name in `N`;
* `FTerm.AvoidsNames N t`: every head of `t` avoids `N`. For a decidable `N` the condition is
  decidable (`Term.decidableHeadsSubset`), so `decide` checks it on concrete terms; for vectors of
  terms it is `Vec.AvoidsNames`, decidable entry by entry;
* `FTerm.denote_update_eq_of_avoidsNames`: the pointwise reading of such a term is unchanged when
  a coordinate of the honest tape that belongs to a name in `N` is overwritten. It is PolyFun's
  `Term.denote_update_eq`: every head the term uses is read independently of that coordinate.

The decision procedure asks the arguments of each constructor of `fullSig D` to be finite, which
`GlobalOp.instFintypeArg` gives for the global constructors.
-/

public section

namespace Interop.Squirrel

open IPFunctor IPFunctor.ScopedSignature

variable {B : Type} {D : Decl B}

/-! ## Finite arguments -/

/-- The positions of a context of types. -/
private def positions : (τs : List (Ty B)) → List ((τ : Ty B) × ScopedVar τs τ)
  | [] => []
  | τ :: τs => ⟨τ, .zero⟩ :: (positions τs).map fun x => ⟨x.1, .succ x.2⟩

private theorem mem_positions : ∀ {τs : List (Ty B)} (x : (τ : Ty B) × ScopedVar τs τ),
    x ∈ positions τs
  | _ :: _, ⟨_, .zero⟩ => List.mem_cons_self
  | _ :: _, ⟨τ, .succ y⟩ =>
    List.mem_cons_of_mem _ (List.mem_map.2 ⟨⟨τ, y⟩, mem_positions _, rfl⟩)

/-- The positions of a context of types are finite; two are equal when their indices are. -/
@[instance_reducible] def positionFintype (τs : List (Ty B)) :
    Fintype ((τ : Ty B) × ScopedVar τs τ) :=
  haveI : DecidableEq ((τ : Ty B) × ScopedVar τs τ) := fun x y =>
    decidable_of_iff (x.2.index = y.2.index)
      ⟨ScopedVar.sigma_eq_of_index_eq _ _, by rintro rfl; rfl⟩
  Fintype.ofList _ mem_positions

/-- The arguments of every global constructor are finite: `∼` has an argument per side and
position. -/
instance GlobalOp.instFintypeArg {k : Kind B} (o : GlobalOp B k) :
    Fintype ((globalSig B).Arg o) :=
  match o with
  | .top | .bot => inferInstanceAs (Fintype (Fin 0))
  | .and | .or | .imp => inferInstanceAs (Fintype (Fin 2))
  | .all _ | .ex _ | .box | .const _ | .adv _ _ _ => inferInstanceAs (Fintype (Fin 1))
  | .equiv τs _ =>
    haveI := positionFintype τs
    inferInstanceAs (Fintype (Bool × (τ : Ty B) × ScopedVar τs τ))

/-! ## Names a term does not use -/

/-- The name that a head constructs, with its types, if it is a name. -/
@[expose] def headName : (fullSig D).Head → Option ((a : Ty B) × (b : Ty B) × D.Name a b)
  | ⟨_, .inl (.name n)⟩ => some ⟨_, _, n⟩
  | _ => none

/-- The head is not the constructor of a name in `N`. -/
@[expose] def AvoidsNamesAt (N : ((a : Ty B) × (b : Ty B) × D.Name a b) → Prop)
    (h : (fullSig D).Head) : Prop :=
  ∀ n ∈ headName h, ¬ N n

instance AvoidsNamesAt.decidablePred (N : ((a : Ty B) × (b : Ty B) × D.Name a b) → Prop)
    [DecidablePred N] : DecidablePred (AvoidsNamesAt N) :=
  fun h => inferInstanceAs (Decidable (∀ n ∈ headName h, ¬ N n))

/-- No constructor of the term is a name in `N`: the term does not use those names. -/
@[expose] def FTerm.AvoidsNames (N : ((a : Ty B) × (b : Ty B) × D.Name a b) → Prop)
    {Γ : List (Kind B)} {τ : Ty B} (t : FTerm D Γ τ) : Prop :=
  t.heads ⊆ {h | AvoidsNamesAt N h}

/-- Whether a term avoids the names `N`: PolyFun's decision procedure for the heads of a term. -/
instance FTerm.decidableAvoidsNames (N : ((a : Ty B) × (b : Ty B) × D.Name a b) → Prop)
    [DecidablePred N] {Γ : List (Kind B)} {τ : Ty B} (t : FTerm D Γ τ) :
    Decidable (t.AvoidsNames N) :=
  Term.decidableHeadsSubset _ t

/-- No entry of the vector uses a name in `N`. -/
@[expose] def Vec.AvoidsNames (N : ((a : Ty B) × (b : Ty B) × D.Name a b) → Prop)
    {Γ : List (Kind B)} {τs : List (Ty B)} (u : Vec D Γ τs) : Prop :=
  ∀ τ x, (u τ x).AvoidsNames N

/-- Whether a vector avoids the names `N`, decided entry by entry. -/
instance Vec.decidableAvoidsNames (N : ((a : Ty B) × (b : Ty B) × D.Name a b) → Prop)
    [DecidablePred N] {Γ : List (Kind B)} :
    {τs : List (Ty B)} → (u : Vec D Γ τs) → Decidable (u.AvoidsNames N)
  | [], _ => isTrue fun _ x => nomatch x
  | _ :: _, u =>
    haveI := Vec.decidableAvoidsNames N fun _ x => u _ x.succ
    decidable_of_iff ((u _ .zero).AvoidsNames N ∧ Vec.AvoidsNames N fun _ x => u _ x.succ)
      ⟨fun h _ x => by cases x with
        | zero => exact h.1
        | succ x => exact h.2 _ x,
      fun h => ⟨h _ .zero, fun _ x => h _ x.succ⟩⟩

/-- A term that does not use the names `N` reads the same at two honest tapes that differ at one
coordinate of a name in `N`: `Term.denote_update_eq`, since every head it uses ignores that
coordinate. -/
theorem FTerm.denote_update_eq_of_avoidsNames
    {N : ((a : Ty B) × (b : Ty B) × D.Name a b) → Prop} {Γ : List (Kind B)} {τ : Ty B}
    {t : FTerm D Γ τ} (ht : t.AvoidsNames N) (M : Model D) {η : ℕ} [DecidableEq (M.Slot η)]
    (ρa : M.TapeA η) (ρh : M.TapeH η) {k : M.Slot η} (hk : N k.1) (c : M.Coin η k.1.2.1) :
    t.denote (Interpretation.sum (interp M η (ρa, Function.update ρh k c)) (ptGlobal M η)) =
      t.denote (Interpretation.sum (interp M η (ρa, ρh)) (ptGlobal M η)) := by
  refine Term.denote_update_eq (X := fun k : M.Slot η => M.Coin η k.1.2.1)
    (fun ρh => Interpretation.sum (interp M η (ρa, ρh)) (ptGlobal M η)) t
    (fun h hh x y => ?_) ρh c
  have hav : AvoidsNamesAt N h := ht hh
  rcases h with ⟨_, o | o⟩
  · cases o with
    | name n =>
      funext _ i
      refine congrArg (M.sample η _) (Function.update_of_ne (fun he => hav _ rfl ?_) _ _)
      subst he
      exact hk
    | _ => rfl
  · rfl

end Interop.Squirrel
