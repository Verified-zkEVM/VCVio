/-
Copyright (c) 2026 Quang Dao, Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Alexander Hicks
-/

module
public import Init.Data.Vector.Basic

/-!
# Entry-sensitive hypertree iteration

The existing structural layer schedule is expressed over XMSS component callbacks and indexed
positions. `recoverSingletonEntry` applies only when the entry has one layer. Nonfinal entries
recover their signature to obtain the next message and reset this flag for recursive calls.
-/

public section

universe u v

namespace SLHDSA.Hypertree.Program

variable {Position : Nat → Type u} {Y Sig : Type u} {m : Type u → Type v} [Monad m]

/-- Sign at every position, recovering nonfinal signatures and optionally a singleton entry. -/
@[expose] def signLayers
    (next : (r : Nat) → Position (r + 2) → Position (r + 1))
    (signOne : (r : Nat) → Position (r + 1) → Y → m Sig)
    (recoverOne : (r : Nat) → Position (r + 1) → Sig → Y → m Y)
    (recoverSingletonEntry : Bool) : (r : Nat) → Position r → Y → m (Vector Sig r)
  | 0, _, _ => pure #v[]
  | 1, position, message => do
      let signature ← signOne 0 position message
      if recoverSingletonEntry then
        let _ ← recoverOne 0 position signature message
        return #v[signature]
      else return #v[signature]
  | r + 2, position, message => do
      let signature ← signOne (r + 1) position message
      let root ← recoverOne (r + 1) position signature message
      let rest ← signLayers next signOne recoverOne false (r + 1) (next r position) root
      return rest.insertIdx 0 signature

/-- Recover one root per layer, including the last layer, using each root as the next message. -/
@[expose] def recoverLayers
    (next : (r : Nat) → Position (r + 2) → Position (r + 1))
    (recoverOne : (r : Nat) → Position (r + 1) → Sig → Y → m Y) :
    (r : Nat) → Position r → Y → Vector Sig r → m Y
  | 0, _, message, _ => pure message
  | 1, position, message, signatures => recoverOne 0 position signatures.head message
  | r + 2, position, message, signatures => do
      let root ← recoverOne (r + 1) position signatures.head message
      recoverLayers next recoverOne (r + 1) (next r position) root signatures.tail

/-- A zero-layer entry returns no signatures and performs no component action. -/
theorem signLayers_zero
    (next : (r : Nat) → Position (r + 2) → Position (r + 1))
    (signOne : (r : Nat) → Position (r + 1) → Y → m Sig)
    (recoverOne : (r : Nat) → Position (r + 1) → Sig → Y → m Y)
    (flag : Bool) (position : Position 0) (message : Y) :
    signLayers next signOne recoverOne flag 0 position message = pure #v[] := rfl

/-- A singleton skip profile signs and returns without a recovery action. -/
theorem signLayers_one_false
    (next : (r : Nat) → Position (r + 2) → Position (r + 1))
    (signOne : (r : Nat) → Position (r + 1) → Y → m Sig)
    (recoverOne : (r : Nat) → Position (r + 1) → Sig → Y → m Y)
    (position : Position 1) (message : Y) :
    signLayers next signOne recoverOne false 1 position message = (do
      let signature ← signOne 0 position message
      return #v[signature] : m (Vector Sig 1)) := rfl

/-- A singleton recovery profile executes and discards the actual recovery result. -/
theorem signLayers_one_true
    (next : (r : Nat) → Position (r + 2) → Position (r + 1))
    (signOne : (r : Nat) → Position (r + 1) → Y → m Sig)
    (recoverOne : (r : Nat) → Position (r + 1) → Sig → Y → m Y)
    (position : Position 1) (message : Y) :
    signLayers next signOne recoverOne true 1 position message = (do
      let signature ← signOne 0 position message
      let _ ← recoverOne 0 position signature message
      return #v[signature] : m (Vector Sig 1)) := rfl

/-- Every nonfinal entry recovers once and resets the singleton flag before continuing. -/
theorem signLayers_add_two
    (next : (r : Nat) → Position (r + 2) → Position (r + 1))
    (signOne : (r : Nat) → Position (r + 1) → Y → m Sig)
    (recoverOne : (r : Nat) → Position (r + 1) → Sig → Y → m Y)
    (flag : Bool) (r : Nat) (position : Position (r + 2)) (message : Y) :
    signLayers next signOne recoverOne flag (r + 2) position message = (do
      let signature ← signOne (r + 1) position message
      let root ← recoverOne (r + 1) position signature message
      let rest ← signLayers next signOne recoverOne false (r + 1) (next r position) root
      return rest.insertIdx 0 signature : m (Vector Sig (r + 2))) := rfl

/-- Empty root recovery returns its input without executing a component. -/
theorem recoverLayers_zero
    (next : (r : Nat) → Position (r + 2) → Position (r + 1))
    (recoverOne : (r : Nat) → Position (r + 1) → Sig → Y → m Y)
    (position : Position 0) (message : Y) (signatures : Vector Sig 0) :
    recoverLayers next recoverOne 0 position message signatures = pure message := rfl

/-- Singleton recovery executes its component directly. -/
theorem recoverLayers_one
    (next : (r : Nat) → Position (r + 2) → Position (r + 1))
    (recoverOne : (r : Nat) → Position (r + 1) → Sig → Y → m Y)
    (position : Position 1) (message : Y) (signatures : Vector Sig 1) :
    recoverLayers next recoverOne 1 position message signatures =
      recoverOne 0 position signatures.head message := rfl

/-- A nonfinal recovered root becomes the next component's message. -/
theorem recoverLayers_add_two
    (next : (r : Nat) → Position (r + 2) → Position (r + 1))
    (recoverOne : (r : Nat) → Position (r + 1) → Sig → Y → m Y)
    (r : Nat) (position : Position (r + 2)) (message : Y) (signatures : Vector Sig (r + 2)) :
    recoverLayers next recoverOne (r + 2) position message signatures = (do
      let root ← recoverOne (r + 1) position signatures.head message
      recoverLayers next recoverOne (r + 1) (next r position) root signatures.tail) := rfl

end SLHDSA.Hypertree.Program
