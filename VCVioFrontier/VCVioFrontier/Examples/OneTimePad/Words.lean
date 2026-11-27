/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
-- frontier: CslibFrontier.Languages.Probabilistic.Basic

public import VCVioFrontier.OracleComp.Measure
public import Examples.OneTimePad.ComputationalComplexity

/-!
# One-time-pad programs on little-endian words

The word encoding lists the least significant bit first. The encryption and round-trip programs
draw precisely the explicit coins of the VCVio one-time pad and use the same XOR at each bit.
-/

public section

open OracleSpec OracleComp MeasureTheory

namespace VCVioFrontier.OneTimePad

/-- Encode a fixed-width word with the least significant bit first. -/
@[expose] def word {n : ℕ} (w : BitVec n) : List Bool := List.ofFn w.getLsb

@[simp] theorem length_word {n : ℕ} (w : BitVec n) : (word w).length = n := List.length_ofFn

/-- Coordinatewise XOR implements the one-time pad with every fixed key, including the empty key. -/
theorem word_xor {n : ℕ} (key msg : BitVec n) :
    word (key ^^^ msg) = (word key).zipWith Bool.xor (word msg) := by
  apply List.ext_getElem
  · simp [word]
  · intro i h₁ h₂
    simp [word, BitVec.getLsb]

/-- Key generation is VCVio's fair-bit program with its output encoded as a word. -/
@[expose] def keyWords (n : ℕ) : OracleComp coinSpec (List Bool) :=
  word <$> oneTimePad.coinBitVec n

/-- Pack each of the explicitly drawn bits in sampling order. -/
theorem keyWords_eq (n : ℕ) :
    keyWords n = List.ofFn <$> oneTimePad.coinVector n := by
  have hbits (bits : Fin n → Bool) : (oneTimePad.bitVecOfFnLE bits).getLsb = bits :=
    funext (oneTimePad.bitVecOfFnLE_getLsb bits)
  change word <$> (oneTimePad.bitVecOfFnLE <$> oneTimePad.coinVector n) = _
  simp [Functor.map_map, word, hbits]

theorem keyWords_zero : keyWords 0 = pure [] := by simp [keyWords_eq, oneTimePad.coinVector]

theorem keyWords_succ (n : ℕ) :
    keyWords (n + 1) = (do
      let bit ← oneTimePad.fairCoin
      return bit :: (← keyWords n)) := by
  rw [keyWords_eq, keyWords_eq]
  change PFunctor.FreeM.map List.ofFn (PFunctor.FreeM.liftBind (P := coinSpec.toPFunctor) ()
    (fun b => PFunctor.FreeM.map (Fin.cons b) (oneTimePad.coinVector n))) = _
  rw [PFunctor.FreeM.map_liftBind]
  congr 1
  funext b
  simp only [PFunctor.FreeM.pure_bind]
  change List.ofFn <$> (Fin.cons b <$> oneTimePad.coinVector n) =
    ((List.ofFn <$> oneTimePad.coinVector n) >>= fun t => pure (b :: t))
  rw [← map_eq_pure_bind]
  simp [Functor.map_map]

/-- Encrypt a message after reading one fresh key bit for each input bit. -/
@[expose] def encryptWord (msg : List Bool) : OracleComp coinSpec (List Bool) :=
  (fun key => key.zipWith Bool.xor msg) <$> keyWords msg.length

/-- Decrypt with the same sampled key that encrypted the message. -/
@[expose] def roundTripWord (msg : List Bool) : OracleComp coinSpec (List Bool) :=
  (fun key => key.zipWith Bool.xor (key.zipWith Bool.xor msg)) <$> keyWords msg.length

/-- Supply coin responses from a tape. A request on an empty tape fails. -/
@[expose] def tapeBits : QueryImpl coinSpec (StateT (List Bool) Option) :=
  fun _ tape => match tape with
    | [] => none
    | b :: rest => some (b, rest)

/-- Key generation consumes its responses in order and leaves the rest of the tape untouched. -/
theorem keyWords_tapeBits (key rest : List Bool) :
    (simulateQ tapeBits (keyWords key.length)).run (key ++ rest) = some (key, rest) := by
  induction key with
  | nil => rw [List.length_nil, keyWords_zero]; rfl
  | cons b key ih =>
    simp only [List.length_cons, keyWords_succ, simulateQ_bind, simulateQ_pure]
    change (do
      let (bits, unused) ← (simulateQ tapeBits (keyWords key.length)).run (key ++ rest)
      pure (b :: bits, unused)) = _
    rw [ih]
    rfl

/-- Installing the tape handler in the encryption experiment yields fixed-key XOR. -/
theorem encryptWord_tapeBits {n : ℕ} (key msg : BitVec n) (rest : List Bool) :
    (simulateQ tapeBits (encryptWord (word msg))).run (word key ++ rest) =
      some (word (key ^^^ msg), rest) := by
  rw [encryptWord, simulateQ_map, length_word, word_xor]
  change (do
    let (bits, unused) ← (simulateQ tapeBits (keyWords n)).run (word key ++ rest)
    pure (bits.zipWith Bool.xor (word msg), unused)) = _
  have h := keyWords_tapeBits (word key) rest
  rw [length_word] at h
  rw [h]
  rfl

/-- The encoded encryption program is the actual VCVio encryption experiment. -/
theorem encryptWord_eq {n : ℕ} (msg : BitVec n) :
    encryptWord (word msg) = word <$>
      (oneTimePad.coinOneTimePad n).perfectSecrecyCipherGivenMsgExperiment msg := by
  have hsource : (oneTimePad.coinOneTimePad n).perfectSecrecyCipherGivenMsgExperiment msg =
      (fun k : BitVec n => k ^^^ msg) <$> oneTimePad.coinBitVec n := by
    simp [SymmEncAlg.perfectSecrecyCipherGivenMsgExperiment, oneTimePad.coinOneTimePad, monad_norm]
  rw [encryptWord, length_word, keyWords, hsource]
  simp only [Functor.map_map, word_xor]

/-- Decryption with the same key recovers the input on every sampled key. -/
theorem roundTripWord_eq {n : ℕ} (msg : BitVec n) :
    roundTripWord (word msg) = (fun _ : BitVec n => word msg) <$> oneTimePad.coinBitVec n := by
  rw [roundTripWord, length_word, keyWords]
  simp only [Functor.map_map, ← word_xor, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

private theorem fairCoinAnswer_eq :
    (inferInstance : OracleSpec.AnswerMeasure coinSpec) = oneTimePad.fairCoinAnswerMeasure := by
  have ext (μ ν : OracleSpec.AnswerMeasure coinSpec)
      (h : @PFunctor.AnswerMeasure.toMeasure _ _ μ = @PFunctor.AnswerMeasure.toMeasure _ _ ν) :
      μ = ν := by cases μ; cases ν; congr
  apply ext
  funext q
  exact OracleSpec.AnswerMeasure.toMeasure_eq_uniformOn (spec := coinSpec) q

/-- The encrypted word has the pushforward of the uniform law on all fixed-width ciphertexts. -/
theorem encryptWord_law (words : MeasurableSpace (List Bool)) {n : ℕ} (msg : BitVec n) :
    let _ := words
    𝒟[encryptWord (word msg)] =
      Measure.map word (ProbabilityTheory.uniformOn (Set.univ : Set (BitVec n))) := by
  let _ := words
  dsimp only
  rw [encryptWord_eq, evalDist_map_of_discrete]
  apply congrArg (Measure.map word)
  change @PFunctor.FreeM.denote coinSpec.toPFunctor _
    (inferInstance : OracleSpec.AnswerMeasure coinSpec) _ _ _ = _
  rw [fairCoinAnswer_eq]
  exact oneTimePad.denote_coinOneTimePad_cipherGivenMsg_eq_uniform n msg

/-- The two experiments have the same ciphertext measure for any two messages of a fixed width. -/
theorem encryptWord_rows (words : MeasurableSpace (List Bool)) {n : ℕ} (m₀ m₁ : BitVec n) :
    let _ := words
    𝒟[encryptWord (word m₀)] = 𝒟[encryptWord (word m₁)] :=
  (encryptWord_law words m₀).trans (encryptWord_law words m₁).symm

/-- Every key path produces the original message after encryption and decryption. -/
theorem roundTripWord_law (words : MeasurableSpace (List Bool)) {n : ℕ} (msg : BitVec n) :
    let _ := words
    𝒟[roundTripWord (word msg)] = Measure.dirac (word msg) := by
  let _ := words
  dsimp only
  rw [roundTripWord_eq, evalDist_map_of_discrete, Measure.map_const,
    OracleComp.evalDist_apply_univ_eq_one, one_smul]

end VCVioFrontier.OneTimePad
