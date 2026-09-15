/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Examples.InnerProduct.Protocol
public import Examples.InnerProduct.Replay
public import PolyFun.Interaction.TwoParty.PublicCoin

/-!
# The inner-product verifier as a public-coin interaction

This is the same verifier as `accepts`, represented in the existing two-party
interaction interface. Its replay theorem connects source transcripts to the
verifier's public-path semantics at arbitrary folding depth.
-/

public section

namespace InnerProduct

open Interaction Interaction.TwoParty PFunctor.FreeM

variable {F G : Type} [Field F]

/-- Alternating folding messages and public challenges, ending in a witness. -/
@[expose]
def protocolTree (F G : Type) [Field F] : Nat → TypeTree
  | 0 => .node (Witness F 0) (fun _ => .done)
  | r + 1 => .node (FoldMessage F G) (fun _ => .node Fˣ (fun _ => protocolTree F G r))

/-- The prover owns messages and the verifier owns challenges. -/
@[expose]
def protocolRoles (F G : Type) [Field F] : (r : Nat) → RoleDecoration (protocolTree F G r)
  | 0 => ⟨.sender, fun _ => ⟨⟩⟩
  | r + 1 => ⟨.sender, fun _ => ⟨.receiver, fun _ => protocolRoles F G r⟩⟩

/-- The interaction path carrying exactly a public protocol transcript. -/
@[expose]
def transcriptPath : {r : Nat} → Transcript F G r → Path (protocolTree F G r)
  | 0, .terminal w => ⟨w, ⟨⟩⟩
  | _ + 1, .step msg x tail => ⟨msg, ⟨x, transcriptPath tail⟩⟩

/-- The path of a folding transcript exposes its message and challenge. -/
theorem transcriptPath_step {r : Nat} (msg : FoldMessage F G) (x : Fˣ)
    (tail : Transcript F G r) :
    transcriptPath (.step msg x tail) = ⟨msg, ⟨x, transcriptPath tail⟩⟩ := rfl

/-- The seeded causal prover in the ordinary two-party execution interface. -/
@[expose]
def proverStrategy {m : Type → Type} [Monad m] : {r : Nat} → Prover F G r →
    StrategyOver (SyntaxOver.TwoParty.pairedTypeTree m) Participant.focal
      (protocolTree F G r) (protocolRoles F G r) (fun _ => Unit)
  | 0, w => pure ⟨w, ()⟩
  | _ + 1, ⟨msg, next⟩ => pure ⟨msg, fun x => pure (proverStrategy (next x))⟩

variable [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]

/-- Public-coin verifier with separately exposed sampling and continuation. -/
@[expose]
def publicVerifier {m : Type → Type} [Monad m] (sample : m Fˣ) :
    {r : Nat} → Statement F G r →
    StrategyOver (PublicCoinCounterpart.counterpartSyntax m) PUnit.unit
      (protocolTree F G r) (protocolRoles F G r) (fun _ => Bool)
  | 0, s => fun w => pure (accepts s (.terminal w))
  | _ + 1, s => fun msg => pure (sample, fun x => publicVerifier sample (fold s msg x))

/-- Replaying the public verifier computes precisely the specified acceptance
predicate, without drawing new challenges. -/
theorem publicVerifier_replay {m : Type → Type} [Monad m] [LawfulMonad m]
    (sample : m Fˣ) {r : Nat} (s : Statement F G r) (tr : Transcript F G r) :
    PublicCoinCounterpart.replay (publicVerifier sample s) (transcriptPath tr) =
      pure (accepts s tr) := by
  induction tr with
  | terminal w =>
      simp only [publicVerifier, transcriptPath, protocolTree, protocolRoles,
        PublicCoinCounterpart.replay, LawfulMonad.pure_bind]
  | @step r msg x tail ih =>
      rw [transcriptPath_step]
      change (pure (sample, fun y => publicVerifier sample (fold s msg y)) >>= fun next =>
        PublicCoinCounterpart.replay (m := m) (Output := fun _ => Bool)
          (spec := TypeTree.node Fˣ (fun _ => protocolTree F G r))
          (roles := ⟨.receiver, fun _ => protocolRoles F G r⟩)
          next ⟨x, transcriptPath tail⟩) = _
      rw [LawfulMonad.pure_bind]
      exact ih (fold s msg x)

end InnerProduct
