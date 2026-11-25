/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.GroupModel.Typed
public import Mathlib.Data.ZMod.Basic

/-!
# Fixed-basis typed group tests

Concrete coefficient recovery and a scalar-reply execution over `ZMod 7` exercise the public
module interface, including preservation of repeated basis positions.
-/

public section

open OracleComp OracleSpec GroupModel GroupModel.Interaction

namespace GroupModelTest.Typed

private abbrev Scalar := ZMod 7
private abbrev Group := fun _ : Unit => Scalar
private def inputs : Groups Group := fun _ => [2, 2]
local notation "point" =>
  (AlgebraicPoint.ofCoeffs (fun i : Fin (inputs ()).length => (inputs ())[i])
    (fun i => ite (Fin.val i = 0) (3 : Scalar) 4))

example : (point).point = 0 := by decide
example : (point).coeffs ⟨0, by decide⟩ = 3 ∧ (point).coeffs ⟨1, by decide⟩ = 4 := by decide

local notation "output" => (Prod.mk true (fun _ => [point]) : TypedOutput Scalar Bool inputs)

example : (forget inputs output).value.groups () = [0] := by decide
example : (forget inputs output).coefficients () = [[3, 4]] := rfl

example : (((explainedEquivTyped inputs)
    ((explainedEquivTyped inputs).symm output)).2 ()).map AlgebraicPoint.coeffs =
    [fun i => if i.val = 0 then 3 else 4] := by decide

example : ((explainedEquivTyped inputs).symm
    ((explainedEquivTyped inputs) ((explainedEquivTyped inputs).symm output))).val.coefficients
    () = [[3, 4]] := rfl

-- The request sends a group element; the reply supplies a scalar used for the final coefficients.
private def adversary : Adversary Scalar Group Unit Unit (fun _ => Scalar) Scalar where
  main input := do
    let reply ← (explainedSpec Scalar Group Unit (fun _ => Scalar)).query
      (Explained.ofVectors input.groups () (fun _ => [fun _ => 1]))
    return Explained.ofVectors (extend input.groups reply.groups) reply.data
      (fun _ => [fun _ => reply.data])
  algebraic input := by
    constructor
    · exact Explained.valid_ofVectors _ _ _
    intro reply
    exact Explained.valid_ofVectors _ _ _

private def game : QueryImpl (plainSpec Group Unit (fun _ => Scalar)) (OracleComp unifSpec) :=
  fun _ => pure ⟨3, fun _ => []⟩

private theorem game_empty : EmptyGroupReplies game := by
  intro q reply hr
  simp only [game, support_pure, Set.mem_singleton_iff] at hr
  subst reply
  rfl

private def input : Message Unit Group := ⟨(), inputs⟩

example : ofTyped inputs (adversary.toTyped game game_empty input) = adversary.run game input :=
  ofTyped_toTyped adversary game game_empty input

example : (fun out => out.2 () |>.map AlgebraicPoint.point) <$>
    adversary.toTyped game game_empty input = pure [5] := by
  rfl

example : (fun out => out.2 () |>.map (fun p => List.ofFn p.coeffs)) <$>
    adversary.toTyped game game_empty input = pure [[3, 3]] := by
  rfl

-- Empty bases still support the zero point and retain its empty coefficient vector.
/-- The public typed constructor computes on an empty basis. -/
theorem empty_basis_point : (AlgebraicPoint.ofCoeffs (F := ZMod 7) (fun i : Fin 0 => Fin.elim0 i)
    (fun i => Fin.elim0 i)).point = (0 : ZMod 7) := rfl

end GroupModelTest.Typed
