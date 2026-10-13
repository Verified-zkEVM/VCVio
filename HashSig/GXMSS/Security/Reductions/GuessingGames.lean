/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Reductions.SourceGames
import all HashSig.GXMSS.Security.Reductions.SourceGames

/-!
# Guessed Game 5 and Game 6

Games 5 and 6 select a finite epoch, chain and position guess and compare their returned
winning measures with the source Game 4 measure. Unused and failed-consumed histories remain
separate residual events.
-/

public section

namespace GXMSS.Reductions

open Encoding ENNReal OracleComp OracleSpec Security TweakableHash

variable {PP T X H M R E S : Type} {h w v n radix : ℕ}

/-- The independently sampled epoch, chain and paper position used by Game 5. -/
abbrev Guess (h w v : ℕ) := Epoch h × Fin v × Fin (2 ^ w - 1)

/-- The actual finite Game 5 guess space has one positive chain position fewer than `2 ^ w`. -/
theorem guess_cardinality (h w v : ℕ) :
    Fintype.card (Guess h w v) = 2 ^ h * v * (2 ^ w - 1) := by
  simp [Guess, Epoch, Fintype.card_prod, Nat.mul_assoc]

/-- The paper's looser coefficient bounds the exact size of the Game 5 guess space. -/
theorem guess_cardinality_le_paper_coefficient (h w v : ℕ) :
    Fintype.card (Guess h w v) ≤ 2 ^ h * v * 2 ^ w := by
  rw [guess_cardinality]
  exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)

private def guessedEpoch (guess : Guess h w v) : Epoch h := guess.1

private def guessedChain (guess : Guess h w v) : Fin v :=
  let coordinate := guess.2
  coordinate.1

private def guessedPosition (guess : Guess h w v) : Fin (2 ^ w - 1) :=
  let coordinate := guess.2
  coordinate.2

/-- Conditional restriction used only by the joint chain-preimage accounting: every returned
codeword has a coordinate strictly below the maximum digit. Incomparability alone does not imply
this property. -/
@[expose] def NoMaximumOutput
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) : Prop :=
  ∀ pp msg randomizer ep word,
    enc.value pp msg randomizer ep = some word →
      ∃ i : Fin v, (word i).val < 2 ^ w - 1

/-- Two distinct words in the global incomparable code ensure that every successful output
has a digit below the maximum, including when only one of the words can be emitted. -/
theorem noMaximumOutput_of_two_codewords
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w))
    (htwo : ∃ x y : Codeword v (2 ^ w), x ∈ enc.code ∧ y ∈ enc.code ∧ x ≠ y) :
    NoMaximumOutput enc := by
  obtain ⟨x, y, hx, hy, hxy⟩ := htwo
  intro pp msg randomizer ep word hword
  have hw : word ∈ enc.code :=
    enc.mem_code_of_value_eq_some pp msg randomizer ep hword
  have hother : ∃ z : Codeword v (2 ^ w), z ∈ enc.code ∧ word ≠ z := by
    by_cases h : word = x
    · exact ⟨y, hy, by simpa [h] using hxy⟩
    · exact ⟨x, hx, h⟩
  obtain ⟨z, hz, hwz⟩ := hother
  obtain ⟨i, hi⟩ := (enc.incomparable hw hz hwz).1
  exact ⟨i, by have := (z i).isLt; omega⟩

/-- The first forged-word coordinate with a non-maximum digit. -/
def findNonMaximumCoordinate (word : Codeword v (2 ^ w)) : Option (Fin v) :=
  Security.findCoordinate (fun i => (word i).val < 2 ^ w - 1)

/-- A selected non-maximum coordinate has a final chain step after its digit. -/
theorem findNonMaximumCoordinate_sound (word : Codeword v (2 ^ w))
    {i : Fin v} (hi : findNonMaximumCoordinate word = some i) :
    (word i).val < 2 ^ w - 1 :=
  Security.findCoordinate_sound _ hi

/-- The conditional output premise makes the finite coordinate scan succeed. -/
theorem findNonMaximumCoordinate_isSome
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w))
    (hnonmax : NoMaximumOutput enc) (pp : PP) (msg : M) (randomizer : R)
    (ep : Epoch h) (word : Codeword v (2 ^ w))
    (hword : enc.value pp msg randomizer ep = some word) :
    (findNonMaximumCoordinate word).isSome :=
  Security.findCoordinate_isSome _ (hnonmax pp msg randomizer ep word hword)

/-- Game 5 program, with the guess sampled before key generation and adversarial interaction.
Positivity at the GXMSS boundary supplies both finite-sampling instances locally. -/
def gameFive [SampleableType H] [SampleableType R] [DecidableEq H]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (hv : 0 < v) (hw : 0 < w)
    (adv : SchemeAdversary PP H M R h v) : ProbComp (Guess h w v × Result PP H M R h v) := by
  letI : NeZero v := ⟨Nat.ne_of_gt hv⟩
  letI : NeZero (2 ^ w - 1) :=
    ⟨by have := Nat.one_lt_two_pow (by omega : w ≠ 0); omega⟩
  exact do
    let guess ← $ᵗ (Guess h w v)
    let out ← sourceProgram hash enc K adv
    return (guess, out)

/-- Game 5 aborts unless every independently sampled coordinate matches the designated cut. -/
def gameFiveObservation [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (out : Guess h w v × Result PP H M R h v) : Bool :=
  let guess := out.1
  let result := out.2
  let publicKey := result.pk
  let forgery := result.forgery
  let forgedEpoch := forgery.1
  let forgedPayload := forgery.2
  let forgedMessage := forgedPayload.1
  let forgedSignature := forgedPayload.2
  gameFourObservation hash enc K result &&
    match forgedEpochSource result with
    | .successful msg sig =>
      match enc.value publicKey.seed msg sig.randomizer forgedEpoch,
        enc.value publicKey.seed forgedMessage forgedSignature.randomizer forgedEpoch with
      | some honestWord, some forgedWord =>
        match findSmallerCoordinate honestWord forgedWord with
        | none => false
        | some i => decide (guessedEpoch guess = forgedEpoch ∧ guessedChain guess = i ∧
            (guessedPosition guess).val + 1 = (honestWord i).val)
      | _, _ => false
    | _ => false

/-- The selected event for all three forged-epoch histories. Successful histories retain the
original Game 5 cut. Unused and failed-consumed histories use the final chain step at the first
non-maximum forged digit. The existing Game 5 observation remains unchanged. -/
def jointChainObservation [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (out : Guess h w v × Result PP H M R h v) : Bool :=
  let guess := out.1
  let result := out.2
  let forgery := result.forgery
  match forgedEpochSource result with
  | .successful _ _ => gameFiveObservation hash enc K out
  | .unused | .failedConsumed _ =>
    gameFourObservation hash enc K result &&
      match enc.value result.pk.seed forgery.2.1 forgery.2.2.randomizer forgery.1 with
      | none => false
      | some forgedWord =>
        match findNonMaximumCoordinate forgedWord with
        | none => false
        | some i => decide (guessedEpoch guess = forgery.1 ∧ guessedChain guess = i ∧
            (guessedPosition guess).val + 1 = 2 ^ w - 1)

/-- The native output measure of the enlarged sampled event keeps returned false and all
unreturned mass from the original source interaction. -/
noncomputable def jointChainOutputMeasure [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (hv : 0 < v) (hw : 0 < w)
    (adv : SchemeAdversary PP H M R h v) : MeasureTheory.Measure Bool :=
  ProbCompRuntime.probComp.evalDist
    (jointChainObservation hash enc K <$> gameFive hash enc K hv hw adv)

/-- Unconditioned returned winning mass of the enlarged single-selector event. -/
noncomputable def jointChainAdvantage [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (hv : 0 < v) (hw : 0 < w)
    (adv : SchemeAdversary PP H M R h v) : ℝ≥0∞ :=
  jointChainOutputMeasure hash enc K hv hw adv {true}

/-- The native Boolean output measure of the sampled Game 5 program, including returned false
and any unreturned mass from the unchanged source interaction. -/
noncomputable def gameFiveOutputMeasure [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (hv : 0 < v) (hw : 0 < w)
    (adv : SchemeAdversary PP H M R h v) : MeasureTheory.Measure Bool :=
  ProbCompRuntime.probComp.evalDist
    (gameFiveObservation hash enc K <$> gameFive hash enc K hv hw adv)

/-- Game 5's unconditioned returned winning mass under the actual finite sampler. -/
noncomputable def gameFiveAdvantage [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (hv : 0 < v) (hw : 0 < w)
    (adv : SchemeAdversary PP H M R h v) : ℝ≥0∞ :=
  gameFiveOutputMeasure hash enc K hv hw adv {true}

/-- Game 5's independent finite guess preserves the source program's total returned mass.
Consequently the native Boolean Game 4 and Game 5 measures have the same missing mass. -/
theorem gameFiveOutputMeasure_univ_eq_gameFourOutputMeasure_univ
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (hv : 0 < v) (hw : 0 < w)
    (adv : SchemeAdversary PP H M R h v) :
    gameFiveOutputMeasure hash enc K hv hw adv Set.univ =
      gameFourOutputMeasure hash enc K adv Set.univ := by
  have : NeZero v := ⟨Nat.ne_of_gt hv⟩
  have : NeZero (2 ^ w - 1) :=
    ⟨by have := Nat.one_lt_two_pow (by omega : w ≠ 0); omega⟩
  let : MeasurableSpace (Guess h w v × Result PP H M R h v) := ⊤
  let : MeasurableSpace (Result PP H M R h v) := ⊤
  have hprojection :
      𝒟[Prod.snd <$> gameFive hash enc K hv hw adv] =
        𝒟[sourceProgram hash enc K adv] := by
    simp only [gameFive, map_eq_bind_pure_comp, bind_assoc, Function.comp_def,
      pure_bind, bind_pure]
    exact OracleComp.evalDist_bind_const
      ($ᵗ (Guess h w v) : ProbComp (Guess h w v)) (sourceProgram hash enc K adv)
  simp only [gameFiveOutputMeasure, gameFourOutputMeasure,
    ProbCompRuntime.probComp_evalDist]
  rw [evalDist_map_apply _ Measurable.of_discrete MeasurableSet.univ,
    evalDist_map_apply _ Measurable.of_discrete MeasurableSet.univ]
  simp only [Set.preimage_univ]
  change 𝒟[gameFive hash enc K hv hw adv] Set.univ =
    𝒟[sourceProgram hash enc K adv] Set.univ
  calc
    _ = 𝒟[Prod.snd <$> gameFive hash enc K hv hw adv] Set.univ := by
      rw [evalDist_map_apply _ Measurable.of_discrete MeasurableSet.univ]
      simp only [Set.preimage_univ]
    _ = _ := congrArg (fun μ : MeasureTheory.Measure (Result PP H M R h v) =>
      μ Set.univ) hprojection

/-- A returned Game 5 win was already a successful-record Game 4 win. -/
theorem gameFiveObservation_implies_successfulGameFour [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (guess : Guess h w v) (out : Result PP H M R h v)
    (hwin : gameFiveObservation hash enc K (guess, out) = true) :
    successfulGameFourObservation hash enc K out = true := by
  cases hs : forgedEpochSource out with
  | unused => simp [gameFiveObservation, hs] at hwin
  | failedConsumed msg => simp [gameFiveObservation, hs] at hwin
  | successful msg sig =>
    have hwin' := hwin
    simp only [gameFiveObservation, hs, Bool.and_eq_true] at hwin'
    have hfour : gameFourObservation hash enc K out = true := by
      exact hwin'.1
    simpa [successfulGameFourObservation, hs] using hfour

/-- The Game 5 filter rejects an unused forged epoch for every independent guess. -/
theorem gameFiveObservation_unused [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (guess : Guess h w v) (out : Result PP H M R h v)
    (hsource : forgedEpochSource out = .unused) :
    gameFiveObservation hash enc K (guess, out) = false := by
  simp [gameFiveObservation, hsource]

/-- The Game 5 filter also rejects a failed consumed epoch for every guess. -/
theorem gameFiveObservation_failedConsumed [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (guess : Guess h w v) (out : Result PP H M R h v) (msg : M)
    (hsource : forgedEpochSource out = .failedConsumed msg) :
    gameFiveObservation hash enc K (guess, out) = false := by
  simp [gameFiveObservation, hsource]

/-- A returned successful Game 4 win has an actual positive designated cut. The witness comes
from the source signing history and the unchanged Game 1--4 observations. -/
theorem successfulGameFour_designated_coordinate [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v)
    (out : Result PP H M R h v)
    (hout : out ∈ support (sourceProgram hash enc K adv))
    (hwin : successfulGameFourObservation hash enc K out = true) :
    let publicKey := out.pk
    let forgery := out.forgery
    let forgedEpoch := forgery.1
    let forgedPayload := forgery.2
    let forgedMessage := forgedPayload.1
    let forgedSignature := forgedPayload.2
    ∃ msg : M, ∃ sig : GXMSS.Signature R H h v,
      ∃ honestWord forgedWord : Codeword v (2 ^ w), ∃ i : Fin v,
      forgedEpochSource out = .successful msg sig ∧
      enc.value publicKey.seed msg sig.randomizer forgedEpoch = some honestWord ∧
      enc.value publicKey.seed forgedMessage forgedSignature.randomizer forgedEpoch =
        some forgedWord ∧
      Security.findSmallerCoordinate honestWord forgedWord = some i := by
  let publicKey := out.pk
  let secretKey := out.sk
  let forgery := out.forgery
  let forgedEpoch := forgery.1
  let forgedPayload := forgery.2
  let forgedMessage := forgedPayload.1
  let forgedSignature := forgedPayload.2
  cases hs : forgedEpochSource out with
  | unused => simp [successfulGameFourObservation, hs] at hwin
  | failedConsumed msg => simp [successfulGameFourObservation, hs] at hwin
  | successful msg sig =>
    have hfour : gameFourObservation hash enc K out = true := by
      simpa [successfulGameFourObservation, hs] using hwin
    have hfour' := hfour
    simp only [gameFourObservation, Bool.and_eq_true] at hfour'
    have hthree := hfour'.1
    have hthree' := hthree
    simp only [gameThreeObservation, Bool.and_eq_true] at hthree'
    have htwo := hthree'.1
    have htwo' := htwo
    simp only [gameTwoObservation, Bool.and_eq_true] at htwo'
    have hone := htwo'.1
    have hrecord := history_of_successful_source out msg sig hs
    obtain ⟨wr, hsig, hhonest⟩ :=
      sourceProgram_successful_record_signature hash enc K adv out hout
        forgedEpoch msg sig hrecord
    have hhonest' : enc.value publicKey.seed msg sig.randomizer forgedEpoch =
        some wr.1 := by
      rw [hsig]
      simpa [GXMSS.signatureOfWord] using hhonest
    obtain ⟨forgedWord, hforged⟩ := forged_encoding_of_gameOne_win hash enc K out hone
    have hpath : sig.path = forgedSignature.path := by
      have hone' := hone
      simp only [gameOneObservation, Bool.and_eq_true] at hone'
      have hleaf := hone'.2
      have hleafValue : forgedLeaf? hash enc out =
          some (fun i => hash.chain publicKey.seed forgedEpoch i (forgedWord i)
            (2 ^ w - 1 - (forgedWord i).val) (forgedSignature.ots i)) := by
        simp [forgedLeaf?, hforged, publicKey, forgery, forgedEpoch,
          forgedPayload, forgedSignature]
      rw [hleafValue] at hleaf
      have hopening : (secretKey.endpoints forgedEpoch,
          hash.authPath publicKey.seed secretKey.endpoints forgedEpoch) =
          ((fun i => hash.chain publicKey.seed forgedEpoch i (forgedWord i)
            (2 ^ w - 1 - (forgedWord i).val) (forgedSignature.ots i)),
            forgedSignature.path) := by
        simpa [gameOneObservation] using (of_decide_eq_true hleaf)
      rw [hsig]
      have hseed := sourceProgram_support_seed_eq hash enc K adv out hout
      rw [hseed] at hopening
      simpa [GXMSS.signatureOfWord] using congrArg Prod.snd hopening
    have hne : wr.1 ≠ forgedWord :=
      gameThree_successful_words_ne hash enc K out msg sig wr.1 forgedWord
        hs hthree hhonest' hforged hpath
    obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp
      (Security.findSmallerCoordinate_isSome_of_successes enc
        publicKey.seed publicKey.seed msg forgedMessage sig.randomizer
        forgedSignature.randomizer forgedEpoch forgedEpoch
        hhonest' hforged hne)
    exact ⟨msg, sig, wr.1, forgedWord, i, rfl, hhonest', hforged, hi⟩

/-- On a successful Game 4 record with its designated cut, exactly one finite guess passes
Game 5's filter. This is a pointwise statement about returned source results. -/
theorem gameFiveObservation_successful_singleton [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (out : Result PP H M R h v) (msg : M) (sig : GXMSS.Signature R H h v)
    (honestWord forgedWord : Codeword v (2 ^ w)) (i : Fin v)
    (hsource : forgedEpochSource out = .successful msg sig)
    (hhonest :
      let publicKey := out.pk
      let forgery := out.forgery
      enc.value publicKey.seed msg sig.randomizer forgery.1 = some honestWord)
    (hforged :
      let publicKey := out.pk
      let forgery := out.forgery
      let forgedPayload := forgery.2
      let forgedSignature := forgedPayload.2
      enc.value publicKey.seed forgedPayload.1 forgedSignature.randomizer
        forgery.1 = some forgedWord)
    (hi : Security.findSmallerCoordinate honestWord forgedWord = some i)
    (hfour : gameFourObservation hash enc K out = true) :
    ∃ target : Guess h w v, ∀ guess : Guess h w v,
      gameFiveObservation hash enc K (guess, out) = true ↔ guess = target := by
  let forgery := out.forgery
  let forgedEpoch := forgery.1
  have hsmaller := Security.findSmallerCoordinate_sound honestWord forgedWord hi
  have hpositive : 0 < (honestWord i).val := by omega
  let position : Fin (2 ^ w - 1) :=
    ⟨(honestWord i).val - 1, by have := (honestWord i).isLt; omega⟩
  let target : Guess h w v := (forgedEpoch, i, position)
  refine ⟨target, ?_⟩
  intro guess
  have hfilter : gameFiveObservation hash enc K (guess, out) = true ↔
      guessedEpoch guess = forgedEpoch ∧ guessedChain guess = i ∧
        (guessedPosition guess).val + 1 = (honestWord i).val := by
    simp [gameFiveObservation, hfour, hsource, hhonest, hforged, hi,
      forgedEpoch, forgery]
  rw [hfilter]
  constructor
  · rintro ⟨hepoch, hchain, hposition⟩
    rcases guess with ⟨epoch, chain, pos⟩
    simp only [guessedEpoch, guessedChain, guessedPosition] at hepoch hchain hposition
    have hpos : pos = position := by
      apply Fin.ext
      dsimp [position]
      omega
    simp only [target]
    exact Prod.ext hepoch (Prod.ext hchain hpos)
  · intro hguess
    subst guess
    simp only [target, guessedEpoch, guessedChain, guessedPosition,
      position, Fin.val_mk, true_and]
    omega

/-- An unused or failed-consumed returned win with a non-maximum forged digit has exactly one
selected final-step guess. -/
theorem jointChainObservation_nonSuccess_singleton [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (out : Result PP H M R h v) (forgedWord : Codeword v (2 ^ w)) (i : Fin v)
    (hsource : forgedEpochSource out = .unused ∨
      ∃ msg, forgedEpochSource out = .failedConsumed msg)
    (hfour : gameFourObservation hash enc K out = true)
    (hword : enc.value out.pk.seed out.forgery.2.1
      out.forgery.2.2.randomizer out.forgery.1 = some forgedWord)
    (hi : findNonMaximumCoordinate forgedWord = some i) :
    ∃ target : Guess h w v, ∀ guess : Guess h w v,
      jointChainObservation hash enc K (guess, out) = true ↔ guess = target := by
  have hmax : 0 < 2 ^ w - 1 := by
    have := findNonMaximumCoordinate_sound forgedWord hi
    omega
  let position : Fin (2 ^ w - 1) := ⟨2 ^ w - 2, by omega⟩
  let target : Guess h w v := (out.forgery.1, i, position)
  refine ⟨target, ?_⟩
  intro guess
  have hfilter : jointChainObservation hash enc K (guess, out) = true ↔
      guessedEpoch guess = out.forgery.1 ∧ guessedChain guess = i ∧
        (guessedPosition guess).val + 1 = 2 ^ w - 1 := by
    rcases hsource with hs | ⟨msg, hs⟩
    · simp [jointChainObservation, hs, hfour, hword, hi]
    · simp [jointChainObservation, hs, hfour, hword, hi]
  rw [hfilter]
  constructor
  · rintro ⟨hepoch, hchain, hposition⟩
    rcases guess with ⟨epoch, chain, pos⟩
    simp only [guessedEpoch, guessedChain, guessedPosition] at hepoch hchain hposition
    have hpos : pos = position := by
      apply Fin.ext
      dsimp [position]
      omega
    exact Prod.ext hepoch (Prod.ext hchain hpos)
  · intro hguess
    subst guess
    simp only [target, guessedEpoch, guessedChain, guessedPosition,
      position, Fin.val_mk, true_and]
    omega

/-- Under the explicit output restriction, every returned Game 4 win has one deterministic
guess in the enlarged selector, regardless of the forged epoch's history class. -/
theorem jointChainObservation_singleton [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v)
    (hnonmax : NoMaximumOutput enc)
    (out : Result PP H M R h v)
    (hout : out ∈ support (sourceProgram hash enc K adv))
    (hfour : gameFourObservation hash enc K out = true) :
    ∃ target : Guess h w v, ∀ guess : Guess h w v,
      jointChainObservation hash enc K (guess, out) = true ↔ guess = target := by
  cases hs : forgedEpochSource out with
  | successful msg sig =>
    obtain ⟨msg', sig', honestWord, forgedWord, i, hsource, hhonest, hforged, hi⟩ :=
      successfulGameFour_designated_coordinate hash enc K adv out hout
        (by simpa [successfulGameFourObservation, hs] using hfour)
    have hsingle := gameFiveObservation_successful_singleton hash enc K out msg' sig'
      honestWord forgedWord i hsource hhonest hforged hi hfour
    obtain ⟨target, htarget⟩ := hsingle
    refine ⟨target, ?_⟩
    intro guess
    simpa [jointChainObservation, hs] using htarget guess
  | unused =>
    have hone : gameOneObservation hash enc K out = true := by
      have hfour' := hfour
      simp only [gameFourObservation, Bool.and_eq_true] at hfour'
      have hthree := hfour'.1
      simp only [gameThreeObservation, Bool.and_eq_true] at hthree
      have htwo := hthree.1
      simp only [gameTwoObservation, Bool.and_eq_true] at htwo
      exact htwo.1
    obtain ⟨word, hword⟩ := forged_encoding_of_gameOne_win hash enc K out hone
    obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp
      (findNonMaximumCoordinate_isSome enc hnonmax _ _ _ _ word hword)
    exact jointChainObservation_nonSuccess_singleton hash enc K out word i
      (Or.inl hs) hfour hword hi
  | failedConsumed msg =>
    have hone : gameOneObservation hash enc K out = true := by
      have hfour' := hfour
      simp only [gameFourObservation, Bool.and_eq_true] at hfour'
      have hthree := hfour'.1
      simp only [gameThreeObservation, Bool.and_eq_true] at hthree
      have htwo := hthree.1
      simp only [gameTwoObservation, Bool.and_eq_true] at htwo
      exact htwo.1
    obtain ⟨word, hword⟩ := forged_encoding_of_gameOne_win hash enc K out hone
    obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp
      (findNonMaximumCoordinate_isSome enc hnonmax _ _ _ _ word hword)
    exact jointChainObservation_nonSuccess_singleton hash enc K out word i
      (Or.inr ⟨msg, hs⟩) hfour hword hi

/-- Every enlarged selected win is still a returned Game 4 win. -/
theorem jointChainObservation_implies_gameFour [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (guess : Guess h w v) (out : Result PP H M R h v)
    (hwin : jointChainObservation hash enc K (guess, out) = true) :
    gameFourObservation hash enc K out = true := by
  cases hs : forgedEpochSource out with
  | successful msg sig =>
    have hfive : gameFiveObservation hash enc K (guess, out) = true := by
      simpa [jointChainObservation, hs] using hwin
    simpa [successfulGameFourObservation, hs] using
      gameFiveObservation_implies_successfulGameFour hash enc K guess out hfive
  | unused =>
    have h := hwin
    simp only [jointChainObservation, hs, Bool.and_eq_true] at h
    exact h.1
  | failedConsumed msg =>
    have h := hwin
    simp only [jointChainObservation, hs, Bool.and_eq_true] at h
    exact h.1

/-- A successful selected history reveals its guessed chain only strictly after every earlier
hybrid cut. This is the event-side guard used by the adaptive source-to-hybrid coupling. -/
private theorem jointChainObservation_successful_digit_above_cut
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (guess : Guess h w v) (out : Result PP H M R h v)
    (msg : M) (sig : GXMSS.Signature R H h v)
    (honestWord : Codeword v (2 ^ w))
    (hsource : forgedEpochSource out = .successful msg sig)
    (hhonest : enc.value out.pk.seed msg sig.randomizer out.forgery.1 =
      some honestWord)
    (hwin : jointChainObservation hash enc K (guess, out) = true)
    (j : Fin (2 ^ w - 1)) (hj : j.val ≤ (guessedPosition guess).val) :
    j.val < (honestWord (guessedChain guess)).val := by
  have hfive : gameFiveObservation hash enc K (guess, out) = true := by
    simpa [jointChainObservation, hsource] using hwin
  have hfilter := hfive
  simp only [gameFiveObservation, hsource, Bool.and_eq_true] at hfilter
  have hselected := hfilter.2
  simp only [hhonest] at hselected
  cases hforged : enc.value out.pk.seed out.forgery.2.1
      out.forgery.2.2.randomizer out.forgery.1 with
  | none => simp [hforged] at hselected
  | some forgedWord =>
    cases hi : findSmallerCoordinate honestWord forgedWord with
    | none => simp [hforged, hi] at hselected
    | some i =>
      simp only [hforged, hi] at hselected
      have hguess : guessedEpoch guess = out.forgery.1 ∧
          guessedChain guess = i ∧
          (guessedPosition guess).val + 1 = (honestWord i).val := by
        exact of_decide_eq_true hselected
      rw [hguess.2.1]
      omega

/-- A selected successful outcome exposes the encoded words and the unique designated cut
chosen by the Game 5 branch. -/
private theorem jointChainObservation_successful_cut
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (guess : Guess h w v) (out : Result PP H M R h v)
    (msg : M) (sig : GXMSS.Signature R H h v)
    (hsource : forgedEpochSource out = .successful msg sig)
    (hwin : jointChainObservation hash enc K (guess, out) = true) :
    ∃ honestWord forgedWord : Codeword v (2 ^ w), ∃ i : Fin v,
      gameFourObservation hash enc K out = true ∧
      enc.value out.pk.seed msg sig.randomizer out.forgery.1 = some honestWord ∧
      enc.value out.pk.seed out.forgery.2.1 out.forgery.2.2.randomizer
        out.forgery.1 = some forgedWord ∧
      findSmallerCoordinate honestWord forgedWord = some i ∧
      guessedEpoch guess = out.forgery.1 ∧ guessedChain guess = i ∧
      (guessedPosition guess).val + 1 = (honestWord i).val := by
  have hfive : gameFiveObservation hash enc K (guess, out) = true := by
    simpa [jointChainObservation, hsource] using hwin
  have hfilter := hfive
  simp only [gameFiveObservation, hsource, Bool.and_eq_true] at hfilter
  have hfour := hfilter.1
  have hselected := hfilter.2
  cases hhonest : enc.value out.pk.seed msg sig.randomizer out.forgery.1 with
  | none => simp [hhonest] at hselected
  | some honestWord =>
    cases hforged : enc.value out.pk.seed out.forgery.2.1
        out.forgery.2.2.randomizer out.forgery.1 with
    | none => simp [hhonest, hforged] at hselected
    | some forgedWord =>
      cases hi : findSmallerCoordinate honestWord forgedWord with
      | none => simp [hhonest, hforged, hi] at hselected
      | some i =>
        simp only [hhonest, hforged, hi] at hselected
        have hguess := of_decide_eq_true hselected
        exact ⟨honestWord, forgedWord, i, hfour, rfl, rfl, hi,
          hguess.1, hguess.2.1, hguess.2.2⟩

/-- One uniform selector succeeds with exactly inverse-cardinality probability on each returned
Game 4 win under the explicit no-maximum-output premise. -/
theorem jointChainGuess_probability [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)] [NeZero v] [NeZero (2 ^ w - 1)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v) (hnonmax : NoMaximumOutput enc)
    (out : Result PP H M R h v)
    (hout : out ∈ support (sourceProgram hash enc K adv)) :
    Pr{let guess ← ($ᵗ (Guess h w v) : ProbComp (Guess h w v))}[
      jointChainObservation hash enc K (guess, out) = true] =
      if gameFourObservation hash enc K out = true then
        (Fintype.card (Guess h w v) : ℝ≥0∞)⁻¹ else 0 := by
  by_cases hwin : gameFourObservation hash enc K out = true
  · obtain ⟨target, htarget⟩ :=
      jointChainObservation_singleton hash enc K adv hnonmax out hout hwin
    simp only [hwin, ite_true]
    rw [prEvent_congr _ _ _ htarget]
    exact SampleableType.prEvent_uniformSample_eq_singleton target
  · have hfalse : gameFourObservation hash enc K out = false := by
      cases h : gameFourObservation hash enc K out <;> simp_all
    simp only [hfalse, Bool.false_eq_true, ite_false]
    apply (SampleableType.prEvent_uniformSample_eq_zero_iff
      (fun guess : Guess h w v => jointChainObservation hash enc K (guess, out) = true)).2
    intro guess hguess
    exact hwin (jointChainObservation_implies_gameFour hash enc K guess out hguess)

/-- Conditional on one returned source result, the actual uniform Game 5 guess passes with
exactly inverse-cardinality mass when that result is a successful Game 4 win. -/
theorem gameFiveGuess_probability [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)] [NeZero v] [NeZero (2 ^ w - 1)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (adv : SchemeAdversary PP H M R h v)
    (out : Result PP H M R h v)
    (hout : out ∈ support (sourceProgram hash enc K adv)) :
    Pr{let guess ← ($ᵗ (Guess h w v) : ProbComp (Guess h w v))}[
      gameFiveObservation hash enc K (guess, out) = true] =
      if successfulGameFourObservation hash enc K out = true then
        (Fintype.card (Guess h w v) : ℝ≥0∞)⁻¹ else 0 := by
  by_cases hwin : successfulGameFourObservation hash enc K out = true
  · obtain ⟨msg, sig, honestWord, forgedWord, i, hsource, hhonest, hforged, hi⟩ :=
      successfulGameFour_designated_coordinate hash enc K adv out hout hwin
    obtain ⟨target, htarget⟩ := gameFiveObservation_successful_singleton
      hash enc K out msg sig honestWord forgedWord i hsource hhonest hforged hi
      (by simpa [successfulGameFourObservation, hsource] using hwin)
    simp only [hwin, ite_true]
    rw [prEvent_congr _ _ _ htarget]
    exact SampleableType.prEvent_uniformSample_eq_singleton target
  · have hfalse : successfulGameFourObservation hash enc K out = false := by
      cases h : successfulGameFourObservation hash enc K out <;> simp_all
    simp only [hfalse, Bool.false_eq_true, ite_false]
    apply (SampleableType.prEvent_uniformSample_eq_zero_iff
      (fun guess : Guess h w v => gameFiveObservation hash enc K (guess, out) = true)).2
    intro guess hguess
    exact hwin (gameFiveObservation_implies_successfulGameFour
      hash enc K guess out hguess)

/-- The actual Game 5 native returned winning mass is exactly the successful-record Game 4
mass divided by the finite guess count. The source program's unreturned mass is unchanged. -/
theorem gameFiveAdvantage_eq_successfulGameFourMass_div_guess_card
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (hv : 0 < v) (hw : 0 < w)
    (adv : SchemeAdversary PP H M R h v) :
    gameFiveAdvantage hash enc K hv hw adv =
      (Fintype.card (Guess h w v) : ℝ≥0∞)⁻¹ *
        successfulGameFourMass hash enc K adv := by
  have : NeZero v := ⟨Nat.ne_of_gt hv⟩
  have : NeZero (2 ^ w - 1) :=
    ⟨by have := Nat.one_lt_two_pow (by omega : w ≠ 0); omega⟩
  let : MeasurableSpace (Result PP H M R h v) := ⊤
  let source := sourceProgram hash enc K adv
  let c : ℝ≥0∞ := (Fintype.card (Guess h w v) : ℝ≥0∞)⁻¹
  have hmass : successfulGameFourMass hash enc K adv =
      𝒟[source] {out | successfulGameFourObservation hash enc K out = true} := by
    simp only [successfulGameFourMass, ProbCompRuntime.probComp_evalDist]
    rw [evalDist_map_apply source Measurable.of_discrete (measurableSet_singleton true)]
    rfl
  have hswap :
      𝒟[gameFiveObservation hash enc K <$> gameFive hash enc K hv hw adv] =
        𝒟[do
          let out ← source
          let guess ← ($ᵗ (Guess h w v) : ProbComp (Guess h w v))
          return gameFiveObservation hash enc K (guess, out)] := by
    simp only [gameFive, map_eq_bind_pure_comp, bind_assoc, pure_bind]
    exact OracleComp.evalDist_bind_bind_swap _ _ _
  have hconditional : ∀ out ∈ support source,
      𝒟[do
        let guess ← ($ᵗ (Guess h w v) : ProbComp (Guess h w v))
        return gameFiveObservation hash enc K (guess, out)] {true} =
        if successfulGameFourObservation hash enc K out = true then c else 0 := by
    intro out hout
    have hprob := gameFiveGuess_probability hash enc K adv out hout
    have hobs : Pr{let guess ← ($ᵗ (Guess h w v) : ProbComp (Guess h w v))}[
        gameFiveObservation hash enc K (guess, out) = true] =
        𝒟[(fun guess => gameFiveObservation hash enc K (guess, out)) <$>
          ($ᵗ (Guess h w v) : ProbComp (Guess h w v))] {true} := by
      exact (prEvent_map _ (fun guess => gameFiveObservation hash enc K (guess, out))
        (fun b => b = true)).symm.trans (prEvent_eq_evalDist_singleton _ true)
    rw [hobs] at hprob
    simpa only [c, map_eq_bind_pure_comp, Function.comp_def] using hprob
  have hae : ∀ᵐ out ∂𝒟[source],
      𝒟[do
        let guess ← ($ᵗ (Guess h w v) : ProbComp (Guess h w v))
        return gameFiveObservation hash enc K (guess, out)] {true} =
        if successfulGameFourObservation hash enc K out = true then c else 0 :=
    evalDist.ae_of_forall_mem_support source _ MeasurableSet.of_discrete hconditional
  unfold gameFiveAdvantage gameFiveOutputMeasure
  rw [ProbCompRuntime.probComp_evalDist, hswap, evalDist_bind_of_discrete,
    MeasureTheory.Measure.bind_apply (measurableSet_singleton true)
      Measurable.of_discrete.aemeasurable, MeasureTheory.lintegral_congr_ae hae]
  have hfun : (fun out : Result PP H M R h v =>
      if successfulGameFourObservation hash enc K out = true then c else 0) =
      ({out | successfulGameFourObservation hash enc K out = true} : Set _).indicator
        (fun _ => c) := by
    funext out
    by_cases h : successfulGameFourObservation hash enc K out = true <;> simp [h]
  rw [hfun, MeasureTheory.lintegral_indicator_const MeasurableSet.of_discrete,
    ← hmass]

/-- On successful returned Game 4 records, the exact finite guess factor recovers the native
Game 4 mass from the actual Game 5 returned winning mass. -/
theorem successfulGameFourMass_eq_guess_card_mul_gameFiveAdvantage
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (hv : 0 < v) (hw : 0 < w)
    (adv : SchemeAdversary PP H M R h v) :
    successfulGameFourMass hash enc K adv =
      (Fintype.card (Guess h w v) : ℝ≥0∞) *
        gameFiveAdvantage hash enc K hv hw adv := by
  have hcard : 0 < Fintype.card (Guess h w v) := by
    rw [guess_cardinality]
    have hpow : 0 < 2 ^ h := pow_pos (by omega) _
    have hposition : 0 < 2 ^ w - 1 := by
      have := Nat.one_lt_two_pow (by omega : w ≠ 0)
      omega
    positivity
  have hne : (Fintype.card (Guess h w v) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hcard
  have htop : (Fintype.card (Guess h w v) : ℝ≥0∞) ≠ ∞ :=
    ENNReal.natCast_ne_top _
  rw [gameFiveAdvantage_eq_successfulGameFourMass_div_guess_card
    hash enc K hv hw adv, ENNReal.mul_inv_cancel_left hne htop]

/-- The enlarged single selector exactly accounts for all returned Game 4 wins, including
unused and failed-consumed forged epochs. Returned false and missing mass stay unconditioned. -/
theorem jointChainAdvantage_eq_gameFourAdvantage_div_guess_card
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (hv : 0 < v) (hw : 0 < w)
    (adv : SchemeAdversary PP H M R h v) (hnonmax : NoMaximumOutput enc) :
    jointChainAdvantage hash enc K hv hw adv =
      (Fintype.card (Guess h w v) : ℝ≥0∞)⁻¹ *
        gameFourAdvantage hash enc K adv := by
  have : NeZero v := ⟨Nat.ne_of_gt hv⟩
  have : NeZero (2 ^ w - 1) :=
    ⟨by have := Nat.one_lt_two_pow (by omega : w ≠ 0); omega⟩
  let : MeasurableSpace (Result PP H M R h v) := ⊤
  let source := sourceProgram hash enc K adv
  let c : ℝ≥0∞ := (Fintype.card (Guess h w v) : ℝ≥0∞)⁻¹
  have hmass : gameFourAdvantage hash enc K adv =
      𝒟[source] {out | gameFourObservation hash enc K out = true} := by
    simp only [gameFourAdvantage, gameFourOutputMeasure, gameFour,
      ProbCompRuntime.probComp_evalDist]
    rw [evalDist_map_apply source Measurable.of_discrete (measurableSet_singleton true)]
    rfl
  have hswap :
      𝒟[jointChainObservation hash enc K <$> gameFive hash enc K hv hw adv] =
        𝒟[do
          let out ← source
          let guess ← ($ᵗ (Guess h w v) : ProbComp (Guess h w v))
          return jointChainObservation hash enc K (guess, out)] := by
    simp only [gameFive, map_eq_bind_pure_comp, bind_assoc, pure_bind]
    exact OracleComp.evalDist_bind_bind_swap _ _ _
  have hconditional : ∀ out ∈ support source,
      𝒟[do
        let guess ← ($ᵗ (Guess h w v) : ProbComp (Guess h w v))
        return jointChainObservation hash enc K (guess, out)] {true} =
        if gameFourObservation hash enc K out = true then c else 0 := by
    intro out hout
    have hprob := jointChainGuess_probability hash enc K adv hnonmax out hout
    have hobs : Pr{let guess ← ($ᵗ (Guess h w v) : ProbComp (Guess h w v))}[
        jointChainObservation hash enc K (guess, out) = true] =
        𝒟[(fun guess => jointChainObservation hash enc K (guess, out)) <$>
          ($ᵗ (Guess h w v) : ProbComp (Guess h w v))] {true} := by
      exact (prEvent_map _ (fun guess => jointChainObservation hash enc K (guess, out))
        (fun b => b = true)).symm.trans (prEvent_eq_evalDist_singleton _ true)
    rw [hobs] at hprob
    simpa only [c, map_eq_bind_pure_comp, Function.comp_def] using hprob
  have hae : ∀ᵐ out ∂𝒟[source],
      𝒟[do
        let guess ← ($ᵗ (Guess h w v) : ProbComp (Guess h w v))
        return jointChainObservation hash enc K (guess, out)] {true} =
        if gameFourObservation hash enc K out = true then c else 0 :=
    evalDist.ae_of_forall_mem_support source _ MeasurableSet.of_discrete hconditional
  unfold jointChainAdvantage jointChainOutputMeasure
  rw [ProbCompRuntime.probComp_evalDist, hswap, evalDist_bind_of_discrete,
    MeasureTheory.Measure.bind_apply (measurableSet_singleton true)
      Measurable.of_discrete.aemeasurable, MeasureTheory.lintegral_congr_ae hae]
  have hfun : (fun out : Result PP H M R h v =>
      if gameFourObservation hash enc K out = true then c else 0) =
      ({out | gameFourObservation hash enc K out = true} : Set _).indicator
        (fun _ => c) := by
    funext out
    by_cases h : gameFourObservation hash enc K out = true <;> simp [h]
  rw [hfun, MeasureTheory.lintegral_indicator_const MeasurableSet.of_discrete,
    ← hmass]

/-- Exact finite-selector accounting for all returned Game 4 winning mass. -/
theorem gameFourAdvantage_eq_guess_card_mul_jointChainAdvantage
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (hv : 0 < v) (hw : 0 < w)
    (adv : SchemeAdversary PP H M R h v) (hnonmax : NoMaximumOutput enc) :
    gameFourAdvantage hash enc K adv =
      (Fintype.card (Guess h w v) : ℝ≥0∞) *
        jointChainAdvantage hash enc K hv hw adv := by
  have hcard : 0 < Fintype.card (Guess h w v) := by
    rw [guess_cardinality]
    have hpow : 0 < 2 ^ h := pow_pos (by omega) _
    have hposition : 0 < 2 ^ w - 1 := by
      have := Nat.one_lt_two_pow (by omega : w ≠ 0)
      omega
    positivity
  have hne : (Fintype.card (Guess h w v) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hcard
  have htop : (Fintype.card (Guess h w v) : ℝ≥0∞) ≠ ∞ :=
    ENNReal.natCast_ne_top _
  rw [jointChainAdvantage_eq_gameFourAdvantage_div_guess_card
    hash enc K hv hw adv hnonmax, ENNReal.mul_inv_cancel_left hne htop]

/-- The native returned-measure Game 4→5 bound before either non-success mass has been charged.
The two residual terms retain unused-query and failed-consumed outcomes separately. -/
theorem gameFourAdvantage_le_gameFive_add_unpaid_masses
    [SampleableType H] [SampleableType R]
    [DecidableEq H] [DecidableEq M] [DecidableEq R]
    [DecidableEq (GXMSS.Signature R H h v)]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (hv : 0 < v) (hw : 0 < w)
    (adv : SchemeAdversary PP H M R h v) :
    gameFourAdvantage hash enc K adv ≤
      (Fintype.card (Guess h w v) : ℝ≥0∞) *
        gameFiveAdvantage hash enc K hv hw adv +
          unusedGameFourMass hash enc K adv +
            failedConsumedGameFourMass hash enc K adv := by
  calc
    gameFourAdvantage hash enc K adv ≤
        successfulGameFourMass hash enc K adv +
          nonSuccessGameFourMass hash enc K adv :=
      gameFourAdvantage_le_successful_add_nonSuccess hash enc K adv
    _ ≤ successfulGameFourMass hash enc K adv +
        (unusedGameFourMass hash enc K adv +
          failedConsumedGameFourMass hash enc K adv) := by
      gcongr
      exact nonSuccessGameFourMass_le_unused_add_failedConsumed hash enc K adv
    _ = _ := by
      rw [successfulGameFourMass_eq_guess_card_mul_gameFiveAdvantage
        hash enc K hv hw adv]
      ac_rfl

end GXMSS.Reductions
