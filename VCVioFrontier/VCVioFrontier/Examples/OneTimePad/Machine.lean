/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
-- frontier: CslibFrontier.Computability.Probabilistic.Sampling

public import VCVioFrontier.Examples.OneTimePad.Words
public import VCVioFrontier.OracleComp.Realization
public import PolyFunFrontier.IPFunctor.Scoped.PolyTime

/-!
# The one-time pad on uniformly clocked fair-coin machines

The multi-tape machines in this module realize the word programs that encode VCVio's typed
one-time pad. Their output laws and halting proofs use the same machine and clock at every width.
-/

public section

open MeasureTheory Turing.MultiTapeTM PFunctor.FreeM

namespace VCVioFrontier.OneTimePad

private theorem fairCoin_liftM :
    PFunctor.FreeM.liftM (P := coinSpec.toPFunctor) (m := Cslib.ProbComp)
      fairBits oneTimePad.fairCoin = Cslib.ProbComp.uniform Bool :=
  PFunctor.FreeM.liftM_lift (m := Cslib.ProbComp) (P := coinSpec.toPFunctor) fairBits ()

private theorem keyWords_sampleBits (n : ℕ) :
    sampleBits oneTimePad.fairCoin n = keyWords n := by
  induction n with
  | zero => exact keyWords_zero.symm
  | succ n ih => rw [sampleBits, keyWords_succ, ih]

/-- The unary security parameter is the input of a single strict-PPT key generator. -/
theorem keyWords_certificate :
    PPTProgram (P := coinSpec.toPFunctor) fairBits encUnary encBits keyWords :=
  (PPTProgram.sampleBits (count := id) fairCoin_liftM ComputableInPolyTime.id').congr
    keyWords_sampleBits

/-- At clock `n + 1`, the scanner on unary input `n` has the law of the encoded keys. -/
theorem keyWords_linear_machine (n : ℕ) :
    Cslib.ProbComp.eval (Turing.MultiTapePTM.uniformListMachine.runClosed (n + 1) (encUnary n)) =
      Cslib.ProbComp.eval (simulateQ fairBits (keyWords n)) := by
  rw [← keyWords_sampleBits]
  change _ = Cslib.ProbComp.eval ((sampleBits oneTimePad.fairCoin n).liftM fairBits)
  rw [liftM_sampleBits fairCoin_liftM, Cslib.BitString.eval_sampleList]
  simpa only [encUnary_apply, List.length_replicate] using
    Turing.MultiTapePTM.eval_uniformListMachine (encUnary n)

open IPFunctor.ScopedSignature in
/-- Sample a key, then evaluate the scoped expression `key xor msg` with the sampled bits. -/
theorem encryptWord_certificate :
    PPTProgram (P := coinSpec.toPFunctor) fairBits encBits encBits encryptWord := by
  have draw := keyWords_certificate.preprocess ComputableInPolyTime.length_bits
  apply draw.mapWith (f := fun msg key => key.zipWith Bool.xor msg)
  simpa only [Binary.denote_app, Binary.denote_fst, Binary.denote_snd] using
    wordTerm_polyTime (Binary.app Bool.xor Binary.snd Binary.fst)

open IPFunctor.ScopedSignature in
/-- The scoped expression `key xor (key xor msg)` uses the same sampled key in both places. -/
theorem roundTripWord_certificate :
    PPTProgram (P := coinSpec.toPFunctor) fairBits encBits encBits roundTripWord := by
  have draw := keyWords_certificate.preprocess ComputableInPolyTime.length_bits
  apply draw.mapWith (f := fun msg key => key.zipWith Bool.xor (key.zipWith Bool.xor msg))
  simpa only [Binary.denote_app, Binary.denote_fst, Binary.denote_snd] using
    wordTerm_polyTime (Binary.app Bool.xor Binary.snd (Binary.app Bool.xor Binary.snd Binary.fst))

/-- A fixed machine realizing a word computation with its coin requests interpreted fairly. -/
abbrev WordMachine {α : Type} (input : α ↪ List Bool)
    (program : α → OracleComp coinSpec (List Bool)) :=
  MachineRealization (P := coinSpec.toPFunctor) fairBits input encBits program

/-- Encoded output at the implementation's certified clock. -/
noncomputable abbrev WordMachine.output {α : Type} {input : α ↪ List Bool} {p}
    (M : WordMachine input p) (a : α) : PMF (List Bool) :=
  MachineRealization.output M a

/-- The identity word encoding gives agreement with the unchanged sampled output. -/
theorem WordMachine.agrees {α : Type} {input : α ↪ List Bool} {p}
    (M : WordMachine input p) (a : α) :
    M.output a = Cslib.ProbComp.eval (simulateQ fairBits (p a)) := by
  unfold WordMachine.output MachineRealization.output simulateQ
  simpa only [encBits, Function.Embedding.coe_refl, PMF.map_id] using M.encoded_law a

/-- The output at the same clock at which the machine halts has the source program's law. -/
theorem WordMachine.output_law {α : Type} {input : α ↪ List Bool} {p}
    (M : WordMachine input p) (a : α)
    (words : MeasurableSpace (List Bool)) :
    let _ := words
    (M.output a).toMeasure = 𝒟[p a] := by
  let _ := words
  dsimp only
  rw [M.output_measure a words, evalDist_eq_toMeasure, Cslib.ProbComp.eval_map]
  simpa only [encBits, Function.Embedding.coe_refl, PMF.map_id, simulateQ] using
    (evalDist_fairBits (p a)).symm

/-- A fixed fair-coin machine realizing encryption at every message width. -/
noncomputable def encryptMachine : WordMachine encBits encryptWord :=
  MachineRealization.ofPPTProgram encryptWord_certificate

/-- A fixed fair-coin machine realizing the common-key encryption and decryption experiment. -/
noncomputable def roundTripMachine : WordMachine encBits roundTripWord :=
  MachineRealization.ofPPTProgram roundTripWord_certificate

/-- A machine for encryption and decryption with an externally supplied key and data word. -/
noncomputable def xorMachine :
    WordMachine (encPair encBits encBits)
      (fun p : List Bool × List Bool => pure (p.1.zipWith Bool.xor p.2)) :=
  MachineRealization.ofPPTProgram (PPTProgram.localMap IPFunctor.ScopedSignature.wordXor_polyTime)

/-- The machine computes the typed bitwise XOR for each key and message, including keys of
probability zero under any chosen external key distribution. -/
theorem xorMachine_exact {n : ℕ} (k msg : BitVec n) :
    xorMachine.output (word k, word msg) = PMF.pure (word (k ^^^ msg)) := by
  rw [WordMachine.agrees, word_xor]
  rfl

/-- The decryption kernel inverts encryption at the same caller-supplied key. -/
theorem xorMachine_decrypt {n : ℕ} (k msg : BitVec n) :
    xorMachine.output (word k, word (k ^^^ msg)) = PMF.pure (word msg) := by
  rw [xorMachine_exact, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

/-- The machine's ciphertext measure is the encoded uniform measure on the entire message space. -/
theorem encryptMachine_uniform (words : MeasurableSpace (List Bool)) {n : ℕ} (msg : BitVec n) :
    let _ := words
    (encryptMachine.output (word msg)).toMeasure =
      Measure.map word (ProbabilityTheory.uniformOn (Set.univ : Set (BitVec n))) :=
  (encryptMachine.output_law _ words).trans (encryptWord_law words msg)

/-- Every two messages of equal width have the same machine ciphertext distribution. -/
theorem encryptMachine_rows {n : ℕ} (m₀ m₁ : BitVec n) :
    encryptMachine.output (word m₀) = encryptMachine.output (word m₁) := by
  let _ : MeasurableSpace (List Bool) := ⊤
  apply PMF.toMeasure_injective
  exact (encryptMachine.output_law _ ⊤).trans
    ((encryptWord_rows ⊤ m₀ m₁).trans (encryptMachine.output_law _ ⊤).symm)

/-- At its certified clock the round-trip machine outputs the original message with certainty. -/
theorem roundTripMachine_correct {n : ℕ} (msg : BitVec n) :
    roundTripMachine.output (word msg) = PMF.pure (word msg) := by
  let _ : MeasurableSpace (List Bool) := ⊤
  apply PMF.toMeasure_injective
  rw [PMF.toMeasure_pure]
  exact (roundTripMachine.output_law _ ⊤).trans (roundTripWord_law ⊤ msg)

end VCVioFrontier.OneTimePad
