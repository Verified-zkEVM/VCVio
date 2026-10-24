/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Bridge.Round
public import PolyFunCryptol.Translation.Finite.Loop

/-!
# Finite SHA-256 compression implementation

Each schedule entry and round result is bound once. The implementation remains
a finite typed description, so it supports native execution and source export.
The preserved recursive source is certified separately.
-/

public section

namespace Cryptol.Bridge

open Cryptol.Finite

/-- One arbitrary chaining state and one arbitrary 512-bit block. -/
abbrev CompressionInput : Finite.Ty := .prod RoundOutput (.seq 16 (.word 32))

/-- The fully represented compression input. -/
@[expose] def compressionInputShape : DataShape CompressionInput :=
  .prod roundOutputShape (.seq 16 (.word 32))

/-- A finite schedule equation, using only entries strictly before its index. -/
@[expose] def scheduleStep (block : Fin 16 → BitVec 32) (n : Nat)
    (previous : Fin n → BitVec 32) : BitVec 32 :=
  if h : n < 16 then block ⟨n, h⟩ else
    let s1 : BitVec 32 :=
      Foundation.smallSigma256One.denote Env.empty (previous ⟨n - 2, by omega⟩)
    let s0 : BitVec 32 :=
      Foundation.smallSigma256Zero.denote Env.empty (previous ⟨n - 15, by omega⟩)
    s1 + previous ⟨n - 7, by omega⟩ + s0 + previous ⟨n - 16, by omega⟩

/-- All 64 schedule words with retained intermediate results. -/
@[expose] def schedule256 (block : Fin 16 → BitVec 32) : Fin 64 → BitVec 32 :=
  prefixValues (scheduleStep block) 64

/-- A checked finite description of a schedule coordinate. -/
@[expose] def scheduleStepTerm (n : Nat) :
    Term [.seq n (.word 32), CompressionInput] (.word 32) :=
  if h : n < 16 then .index (.snd (.var (.succ .zero))) ⟨n, h⟩ else
    .arithmetic .add
      (.arithmetic .add
        (.arithmetic .add
          (.app Foundation.smallSigma256OneIn (.index (.var .zero) ⟨n - 2, by omega⟩))
          (.index (.var .zero) ⟨n - 7, by omega⟩))
        (.app Foundation.smallSigma256ZeroIn (.index (.var .zero) ⟨n - 15, by omega⟩)))
      (.index (.var .zero) ⟨n - 16, by omega⟩)

/-- The step description computes the recurrence for every input prefix. -/
theorem scheduleStepTerm_denote (n : Nat) (ρ : Env [CompressionInput])
    (previous : Fin n → BitVec 32) :
    (scheduleStepTerm n).denote (ρ.extend previous) =
      scheduleStep (ρ _ .zero).2 n previous := by
  unfold scheduleStepTerm scheduleStep
  split <;>
    simp [Foundation.smallSigma256One, Foundation.smallSigma256OneIn,
      Foundation.smallSigma256Zero, Foundation.smallSigma256ZeroIn, ArithOp.eval, wordOp]

/-- The compiled schedule. -/
@[expose] def scheduleTerm : Term [CompressionInput] (.seq 64 (.word 32)) :=
  Term.prefixTable scheduleStepTerm 64

/-- All schedule coordinates agree with the shared native recurrence. -/
theorem scheduleTerm_denote (ρ : Env [CompressionInput]) :
    scheduleTerm.denote ρ = schedule256 (ρ _ .zero).2 := by
  rw [scheduleTerm, Term.denote_prefixTable]
  simp only [scheduleStepTerm_denote, schedule256]

/-- One finite round update; only the first 64 updates are used by compression. -/
@[expose] def compressionRound (w : Fin 64 → BitVec 32) (n : Nat)
    (state : Fin 8 → BitVec 32) : Fin 8 → BitVec 32 :=
  if h : n < 64 then
    Foundation.round256Native (state, Foundation.constants256 ⟨n, h⟩, w ⟨n, h⟩)
  else state

/-- Execute the first `n` round updates. -/
@[expose] def compressionRounds (w : Fin 64 → BitVec 32) (initial : Fin 8 → BitVec 32) :
    Nat → Fin 8 → BitVec 32
  | 0 => initial
  | n + 1 => compressionRound w n (compressionRounds w initial n)

/-- A single round reads the constant and the compiled schedule at its fixed index. -/
@[expose] def compressionRoundTerm (n : Nat) :
    Term [RoundOutput, .seq 64 (.word 32), CompressionInput] RoundOutput :=
  if h : n < 64 then .app Foundation.round256In
    (.pair (.var .zero) (.pair (.word (Foundation.constants256 ⟨n, h⟩))
      (.index (.var (.succ .zero)) ⟨n, h⟩)))
  else .var .zero

/-- The round description computes the native register update in arbitrary environments. -/
theorem compressionRoundTerm_denote (n : Nat)
    (ρ : Env [.seq 64 (.word 32), CompressionInput]) (state : Fin 8 → BitVec 32) :
    (compressionRoundTerm n).denote (ρ.extend state) =
      compressionRound (ρ _ .zero) n state := by
  unfold compressionRoundTerm compressionRound
  split
  · simp only [Term.denote_app, Term.denote_pair, Term.denote_var, Term.denote_word,
      Term.denote_index, Env.extend_zero, Env.extend_succ, Foundation.round256In_denote]
  · simp only [Term.denote_var, Env.extend_zero]

/-- The 64 shared round applications. -/
@[expose] def compressionRoundsTerm (n : Nat) :
    Term [.seq 64 (.word 32), CompressionInput] RoundOutput :=
  Term.iterate compressionRoundTerm (.fst (.var (.succ .zero))) n

/-- All intermediate round states agree, including the initial state. -/
theorem compressionRoundsTerm_denote (n : Nat)
    (ρ : Env [.seq 64 (.word 32), CompressionInput]) :
    (compressionRoundsTerm n).denote ρ =
      compressionRounds (ρ _ .zero) (ρ _ (.succ .zero)).1 n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (Term.iterate _ _ (n + 1)).denote ρ = _
      rw [Term.denote_iterate_succ, compressionRoundTerm_denote]
      change compressionRound _ _ ((compressionRoundsTerm n).denote ρ) = _
      rw [ih]
      rfl

/-- Independent native compression, including the final feed-forward. -/
@[expose] def compressionNative (input : CompressionInput.Native) : RoundOutput.Native :=
  let w := schedule256 input.2
  let finalState := compressionRounds w input.1 64
  fun i => BitVec.add (input.1 i) (finalState i)

/-- A finite compression program with shared schedule words and register states. -/
@[expose] def compressionTerm : Term [] (.arrow CompressionInput RoundOutput) :=
  .lam (.letE scheduleTerm (.letE (compressionRoundsTerm 64)
    (.sequence 8 (fun i => .arithmetic .add
      (.index (.fst (.var (.succ (.succ .zero)))) i) (.index (.var .zero) i)))))

/-- The finite description computes the complete compression result for arbitrary data. -/
theorem compressionTerm_denote (input : CompressionInput.Native) :
    compressionTerm.denote Env.empty input = compressionNative input := by
  simp only [compressionTerm, Term.denote_lam, Term.denote_letE, Term.denote_sequence,
    Term.denote_arithmetic, Term.denote_index, Term.denote_fst, Term.denote_var,
    Env.extend_zero, Env.extend_succ, scheduleTerm_denote, compressionRoundsTerm_denote,
    ArithOp.eval, compressionNative]
  rfl

end Cryptol.Bridge
