/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.GroupModel.PairingExplained

/-! # Value-independent metadata for pairing explanations

Chronological coefficient tables can be maintained without access to real group elements.
Replacing all values by zero preserves receipts, table lengths, and outgoing coefficient lists.
The metadata update discards equality replies: a generic interpreter must obtain those replies
from its actual group oracle.
-/

public section

open OracleComp OracleSpec

namespace GroupModel.Pairing

open Interaction

variable {F T : Type} {G : Bool → Type}

/-- Replace source values by scalar zero, retaining every representation and receipt handle. -/
@[expose] def eraseSourceValues [Zero F] (st : GroupModel.Tracked F G) :
    GroupModel.Tracked F (fun _ : Bool => F) :=
  (st.1, mapTbl (fun _ x => (x.1, 0)) st.2)

/-- Replace all pairing values by zero while retaining the complete coefficient metadata. -/
@[expose] def eraseValues [Zero F] (st : Tracked F G T) :
    Tracked F (fun _ : Bool => F) F :=
  (eraseSourceValues st.1, st.2.map fun _ => 0)

private theorem lookup_erase [Zero F] [∀ b, Zero (G b)]
    (tbl : Tbl (fun b => Repr F × G b)) (b : Bool) (h : Handle) :
    lookup (mapTbl (fun _ x => (x.1, (0 : F))) tbl) b h =
      ((lookup tbl b h).1, 0) := by
  exact List.getD_map (tbl b) 0 (fun x => (x.1, (0 : F)))

private theorem eraseSourceValues_groupStep [CommSemiring F] [DecidableEq F]
    [∀ b, AddCommMonoid (G b)] [∀ b, Module F (G b)] [∀ b, DecidableEq (G b)]
    (q : GroupModel.Query F (discreteSig Bool)) (st : GroupModel.Tracked F G) :
    eraseSourceValues (st.1, (groupStep q st.2).2) =
      ((eraseSourceValues st).1, (groupStep q (eraseSourceValues st).2).2) := by
  cases q with
  | add b a c =>
    simp only [groupStep, eraseSourceValues, mapTbl_append, lookup_erase,
      Prod.fst_add, Prod.mk_add_mk, add_zero]
  | smul b c a =>
    simp only [groupStep, eraseSourceValues, mapTbl_append, lookup_erase,
      Prod.smul_fst, Prod.smul_mk, smul_zero]
  | eq b a c => rfl
  | lin o a => exact o.elim
  | bil o a b => exact o.elim

/-- Updating erased metadata agrees with erasing a real step's state.
Equality answers are deliberately absent from this identity. -/
theorem eraseValues_step [CommSemiring F] [DecidableEq F]
    [∀ b, AddCommMonoid (G b)] [∀ b, Module F (G b)] [∀ b, DecidableEq (G b)]
    [AddCommMonoid T] [Module F T] [DecidableEq T]
    (e : G false →ₗ[F] G true →ₗ[F] T)
    (q : GroupModel.Query F pairingSig) (st : Tracked F G T) :
    eraseValues (step e q st).2 =
      (step (0 : F →ₗ[F] F →ₗ[F] F) q (eraseValues st)).2 := by
  cases q with
  | add s a b => cases s with
    | g₁ =>
      exact congrArg (fun x => (x, st.2.map fun _ => (0 : F)))
          (eraseSourceValues_groupStep (.add false a b) st.1)
    | g₂ =>
      exact congrArg (fun x => (x, st.2.map fun _ => (0 : F)))
          (eraseSourceValues_groupStep (.add true a b) st.1)
    | gₜ => simp [step, eraseValues]
  | smul s c a => cases s with
    | g₁ =>
      exact congrArg (fun x => (x, st.2.map fun _ => (0 : F)))
          (eraseSourceValues_groupStep (.smul false c a) st.1)
    | g₂ =>
      exact congrArg (fun x => (x, st.2.map fun _ => (0 : F)))
          (eraseSourceValues_groupStep (.smul true c a) st.1)
    | gₜ => simp [step, eraseValues]
  | eq s a b => cases s <;> rfl
  | lin o a => exact o.elim
  | bil o a b => simp [step, eraseValues]

private theorem eraseSourceValues_receiveAt [Zero F] [One F]
    (st : GroupModel.Tracked F G) (b : Bool) (xs : List (G b)) :
    eraseSourceValues (receiveAt b xs st) =
      receiveAt b (xs.map fun _ => (0 : F)) (eraseSourceValues st) := by
  induction xs generalizing st with
  | nil => rfl
  | cons x xs ih =>
    simp only [receiveAt, List.foldl_cons, List.map_cons] at *
    rw [ih]
    congr 1
    simp only [eraseSourceValues, mapTbl_append, mapTbl, List.length_map]

/-- Installing source replies in erased metadata depends only on their lengths. -/
theorem eraseSourceValues_receive [Zero F] [One F]
    (st : GroupModel.Tracked F G) (xs : Groups G) :
    eraseSourceValues (receive st xs) =
      receive (eraseSourceValues st) (fun b => (xs b).map fun _ => (0 : F)) := by
  apply Prod.ext
  · funext b
    exact congrArg (fun z => z.1 b) (eraseSourceValues_receiveAt st b (xs b))
  · funext b
    exact congrArg (fun z => z.2 b) (eraseSourceValues_receiveAt st b (xs b))

/-- Erasing values preserves every coefficient of an outgoing source explanation. -/
theorem explain_eraseSourceValues_coefficients [Zero F] [∀ b, Zero (G b)]
    {Data : Type} (st : GroupModel.Tracked F G)
    (msg : Message Data (fun _ : Bool => Handle)) :
    (explain (eraseSourceValues st) msg).coefficients = (explain st msg).coefficients := by
  simp only [explain, eraseSourceValues, lookup_erase]

end GroupModel.Pairing
