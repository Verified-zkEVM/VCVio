/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.OracleComp.Coinductive.SecurityFamily

/-!
# Security-family packing checks

Compile-time checks that packing retains the security parameter in inputs, outputs, queries, and
typed continuations, so one aggregate program can be given one uniform realization.
-/

@[expose] public section

#check OracleComp.SecurityFamily.Input
#check OracleComp.SecurityFamily.Output
#check OracleComp.SecurityFamily.Spec
#check OracleComp.SecurityFamily.packComp
#check OracleComp.SecurityFamily.packProgram

namespace OracleComp.SecurityFamily

def bitSpec (_n : Nat) : OracleSpec Unit :=
  fun _ ↦ Bool

def bitProgram (n : Nat) (input : Bool) : OracleComp (bitSpec n) Bool := do
  let coin ← (bitSpec n).query ()
  pure (xor input coin)

example (n : Nat) (input : Bool) :
    packProgram bitProgram ⟨n, input⟩ =
      OracleComp.queryBind (spec := Spec bitSpec) ⟨n, ()⟩
        (fun coin ↦ pure ⟨n, xor input coin⟩) :=
  rfl

example (n : Nat) (value : Bool) :
    packComp (spec := bitSpec) (β := fun _ ↦ Bool) n (pure value) = pure ⟨n, value⟩ := by
  simp

example :
    (⟨0, PUnit.unit⟩ : (Spec bitSpec).Domain) ≠ ⟨1, PUnit.unit⟩ := by
  simp

end OracleComp.SecurityFamily
