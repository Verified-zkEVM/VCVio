/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import VCVio.OracleComp.QueryTracking.RandomOracle.Encoded

/-!
# Completion invariants through ordinary imports

The public interface exposes finite typed support, routed cache coverage and preservation.
These contracts also apply when distinct typed inputs share one encoding.
The aliased Boolean example lives inside a theorem, so it creates no executable encoding table.
-/

public section

open OracleComp OracleSpec

namespace EncodedStateInvTest

variable {ι D M : Type} {spec : OracleSpec ι} [SampleableType M]
  [∀ t, SampleableType (spec.Range t)]

/-- The invariant exposes the finite typed support needed by the completion operation. -/
theorem finite_of_stateInv (E : RandomOracleEncoding spec D M)
    (s : spec.QueryCache × (D →ₒ M).QueryCache) (h : E.StateInv s) :
    {q | (s.1 q).isSome}.Finite :=
  ((E.stateInv_iff s).1 h).1

/-- Finite typed support and conditional routed coverage construct the public invariant. -/
theorem stateInv_of_finite_coverage (E : RandomOracleEncoding spec D M)
    (s : spec.QueryCache × (D →ₒ M).QueryCache)
    (hf : {q | (s.1 q).isSome}.Finite)
    (hc : ¬E.Clash s.1 → ∀ x, (s.2 x).isSome → ∀ q,
      E.route x = some q → (s.1 q).isSome) : E.StateInv s :=
  (E.stateInv_iff s).2 ⟨hf, hc⟩

/-- A routed full read records the typed point without an encoding-injectivity premise. -/
theorem routed_mark_isSome [DecidableEq ι] (E : RandomOracleEncoding spec D M)
    (c : spec.QueryCache) (x : D) (q : ι) (h : E.route x = some q) (a : M) :
    (E.mark c (.inr x) a q).isSome :=
  E.isSome_mark_of_route h a

/-- Every supported completed step preserves the public invariant for arbitrary encodings. -/
theorem stateInv_of_supported_step [DecidableEq ι] [DecidableEq D]
    (E : RandomOracleEncoding spec D M) (q : (spec + (D →ₒ M)).Domain)
    (s : spec.QueryCache × (D →ₒ M).QueryCache) (hs : E.StateInv s)
    (z : (spec + (D →ₒ M)).Range q × (spec.QueryCache × (D →ₒ M).QueryCache))
    (hz : z ∈ support ((E.typedHashImpl q).run s)) : E.StateInv z.2 :=
  E.preservesInv_typedHashImpl_stateInv q s hs z hz

/-- Both Boolean typed inputs may encode the sole raw point while preservation still holds. -/
theorem noninjective_encoding_preserves :
    let E : RandomOracleEncoding (Bool →ₒ Bool) Unit (Bool × Bool) :=
      .ofSplit (Tail := fun _ => Bool) (fun _ => ()) (fun _ => some false)
        (fun _ => rfl) (fun _ => rfl) (fun _ => Equiv.refl _)
    ¬Function.Injective E.encode ∧ QueryImpl.PreservesInv E.typedHashImpl E.StateInv := by
  dsimp only
  refine ⟨?_, RandomOracleEncoding.preservesInv_typedHashImpl_stateInv _⟩
  intro hinj
  have impossible : (true : Bool) = false := hinj (a₁ := true) (a₂ := false) rfl
  cases impossible

end EncodedStateInvTest
