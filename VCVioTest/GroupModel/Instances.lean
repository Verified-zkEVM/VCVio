/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.GroupModel.Tracking
public import Mathlib.Data.ZMod.Basic
import all VCVio.CryptoFoundations.GroupModel.Instances

/-!
# Executable checks of group-model representations

The discrete program combines inputs, tests equality through the value projection,
and uses an invalid handle. Pairing checks exercise the target outer product.
-/

public section

open OracleComp OracleSpec GroupModel

namespace GroupModelTest

/-- The field used by the executable examples. -/
abbrev F := ZMod 7

/-- Two independent input basis entries. -/
@[expose] def inputs : Unit → List F := fun _ => [2, 3]

/-- Addition, scaling, invalid-handle lookup and value-based equality. -/
@[expose] def program : OracleComp (genSpec F (discreteSig Unit)) (Handle × Bool) := do
  let h ← (genSpec F (discreteSig Unit)).query (Sum.inl (.add () 0 1))
  let k ← (genSpec F (discreteSig Unit)).query (Sum.inl (.smul () 3 h))
  let z ← (genSpec F (discreteSig Unit)).query (Sum.inl (.add () k 99))
  let b ← (genSpec F (discreteSig Unit)).query (Sum.inl (.eq () z k))
  pure (z, b)

/-- Execute a probability computation with the first answer at every sampling query. -/
private def firstAnswers {α : Type} (oa : ProbComp α) : α :=
  simulateQ (fun _ => (pure 0 : Id _)) oa

private def tracked := firstAnswers
  (runGen (tracking (Model.discrete (fun _ : Unit => F))) (fun _ => Prod.snd)
    program (trackInputs (F := F) inputs))

private def realRun := firstAnswers
  (runGen (Model.discrete (F := F) (fun _ : Unit => F)) (fun _ => id) program inputs)

example : tracked.1 = (4, true) := by decide
example : realRun.1 = tracked.1 := by decide
example : (mapTbl (fun _ => Prod.snd) tracked.2) () = realRun.2 () := by decide
example : (lookup tracked.2 () 4).2 = 1 := by decide
example : ((List.range 2).map (lookup tracked.2 () 4).1) = [3, 3] := by decide
example : (lookup tracked.2 () 4).1 99 = 0 := by decide
example : (lookup tracked.2 () 4).1.eval (tracked.2 ()) = (lookup tracked.2 () 4).2 := by
  decide

-- Ordinary imports expose the universal run-level invariant and extraction interface.
/-- The tracked output exposes coefficients through an ordinary public import. -/
theorem program_explained (z : (Handle × Bool) × Tbl (fun _ : Unit => GroupModel.Repr F × F))
    (hz : z ∈ support (runGen (tracking (Model.discrete (fun _ : Unit => F)))
      (fun _ => Prod.snd) program (trackInputs (F := F) inputs))) :
    (lookup z.2 () z.1.1).2 =
      (List.zipWith (fun c g => c • g) ((List.range 2).map (lookup z.2 () z.1.1).1)
        ((List.range 2).map fun j => (lookup z.2 () j).2)).sum := by
  have ht := explains_of_mem_support_runGen (explains_trackInputs inputs) program z hz
  exact ht.lookup_eq_zipWith () z.1.1

private def receipt := (pushGiven (F := F) () (2 : F) : StateT _ Id Handle).run tracked.2

example : receipt.1 = 5 := by decide
example : (lookup receipt.2 () 5).1 5 = 1 := by decide
example : (lookup receipt.2 () 5).1 0 = 0 := by decide
example : (lookup receipt.2 () 5).2 = 2 := by decide

private instance : ∀ s, DecidableEq (PFam F F F s)
  | .g₁ => inferInstanceAs (DecidableEq F)
  | .g₂ => inferInstanceAs (DecidableEq F)
  | .gₜ => inferInstanceAs (DecidableEq F)

private def pairing : F →ₗ[F] F →ₗ[F] F := LinearMap.mul F F

private def pairingInputs : Tbl
    (fun s => PFam (GroupModel.Repr F) (GroupModel.Repr F) (ReprT F) s × PFam F F F s)
  | .g₁ => [((Pi.single 0 (1 : F) : GroupModel.Repr F), (2 : F))]
  | .g₂ => [((Pi.single 0 (1 : F) : GroupModel.Repr F), (3 : F))]
  | .gₜ => []

private def pairingProgram : OracleComp (genSpec F pairingSig) Handle := do
  let h ← (genSpec F pairingSig).query (Sum.inl (.bil () 0 0))
  (genSpec F pairingSig).query (Sum.inl (.smul .gₜ 2 h))

private def pairingTracked := firstAnswers
  (runGen (tracking.pairing pairing) (fun _ => Prod.snd) pairingProgram pairingInputs)

private def pairingRealRun := firstAnswers
  (runGen (pairingReal pairing) (fun _ => id) pairingProgram
    (mapTbl (fun _ => Prod.snd) pairingInputs))

private def pairingExecutable : Model F pairingSig
    (fun s => PFam (GroupModel.Repr F) (GroupModel.Repr F) (ReprT F) s × PFam F F F s) where
  lin o := o.elim
  bil _ := (show (GroupModel.Repr F × F) →ₗ[F] (GroupModel.Repr F × F) →ₗ[F]
      (ReprT F × F) from
    LinearMap.mk₂ F (fun x y => (outer F x.1 y.1, pairing x.2 y.2))
      (by intros; simp)
      (by intros; simp [pairing, mul_assoc])
      (by intros; simp)
      (by intros; simp [pairing, mul_left_comm]))

private theorem pairing_model_eq : tracking.pairing pairing = pairingExecutable := by
  have hl : (tracking.pairing pairing).lin = pairingExecutable.lin := by
    funext o
    exact o.elim
  have hb : (tracking.pairing pairing).bil = pairingExecutable.bil := by
    funext o
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    exact Model.prod_bil_apply (free.pairing F) (pairingReal pairing) o x y
  exact congrArg₂ Model.mk hl hb

example : pairingTracked.1 = 1 := by decide
example : (lookup pairingTracked.2 .gₜ 1).2 = (5 : F) := by
  unfold pairingTracked
  rw [pairing_model_eq]
  exact @of_decide_eq_true _ (ZMod.decidableEq 7 _ _) rfl
example : (lookup pairingTracked.2 .gₜ 1).1.1 0 = 0 := by
  unfold pairingTracked
  rw [pairing_model_eq]
  decide
example : (lookup pairingTracked.2 .gₜ 1).1.2 0 0 = 2 := by
  unfold pairingTracked
  rw [pairing_model_eq]
  decide
example : (mapTbl (fun _ => Prod.snd) pairingTracked.2) .gₜ = pairingRealRun.2 .gₜ := by
  unfold pairingTracked
  rw [pairing_model_eq]
  decide
example : evReprT pairing [2] [3] [] (lookup pairingTracked.2 .gₜ 1).1 = 5 := by
  unfold pairingTracked
  rw [pairing_model_eq]
  decide

end GroupModelTest
