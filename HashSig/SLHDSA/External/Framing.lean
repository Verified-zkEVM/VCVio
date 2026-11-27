/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.External

/-!
# Successful pure-context framing

The length-prefixed pure message frame distinguishes its context and payload whenever framing
succeeds. Rejected oversized contexts carry no injectivity claim.
-/

public section

namespace SLHDSA.External

private theorem valid_context_of_frame (context message framed : List Byte)
    (hframe : (encodePureMessage context message).toOption = some framed) :
    context.length ≤ 255 := by
  by_contra h
  simp [encodePureMessage, encodeMessage, requireContext,
    h, Except.toOption] at hframe

/-- Successful frames distinguish different contexts as well as different payloads. -/
theorem encodePureMessage_toOption_injective
    (leftContext leftMessage rightContext rightMessage framed : List Byte)
    (hleft : (encodePureMessage leftContext leftMessage).toOption = some framed)
    (hright : (encodePureMessage rightContext rightMessage).toOption = some framed) :
    leftContext = rightContext ∧ leftMessage = rightMessage := by
  have hl := valid_context_of_frame _ _ _ hleft
  have hr := valid_context_of_frame _ _ _ hright
  rw [encodePureMessage_eq_ok _ _ hl] at hleft
  rw [encodePureMessage_eq_ok _ _ hr] at hright
  have h : (0 : Byte) :: UInt8.ofNat leftContext.length :: (leftContext ++ leftMessage) =
      0 :: UInt8.ofNat rightContext.length :: (rightContext ++ rightMessage) :=
    (Option.some.inj hleft).trans (Option.some.inj hright).symm
  have header := List.cons.inj ((List.cons.inj h).2)
  have hlength := congrArg UInt8.toNat header.1
  have hlLt : leftContext.length < 256 := by omega
  have hrLt : rightContext.length < 256 := by omega
  have hlengthEq : leftContext.length = rightContext.length := by
    simpa only [UInt8.toNat_ofNat', Nat.mod_eq_of_lt hlLt, Nat.mod_eq_of_lt hrLt] using hlength
  have hcontext : leftContext = rightContext := by
    have ht := congrArg (List.take leftContext.length) header.2
    simpa [List.take_append, hlengthEq] using ht
  refine ⟨hcontext, ?_⟩
  simpa only [hcontext, List.append_cancel_left_eq] using header.2

end SLHDSA.External
