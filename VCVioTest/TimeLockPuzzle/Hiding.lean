/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.TimeLockPuzzle.Hiding

/-!
# The hiding game of time-lock puzzles

Checks, through ordinary imports, that the hiding game is neither trivially won nor trivially
lost. The toy puzzle `reveal` asks the random oracle `H : Unit → Bool` in one round and uses the
answer both as the puzzle and as the key, and the DEMs are the one-bit pad and its extension to
lists of bits, keyed by the puzzle with its key through `DEMScheme.comap Prod.snd`, which ignores
the puzzle. An adversary that makes one challenge query and decrypts it with the revealed key
has hiding advantage `1` within zero rounds, so the revealing puzzle is not hiding at any bound
below `1`. An adversary that ignores the challenge oracle has advantage `0`. With the message
length as leakage, a pair of different lengths is answered by `none`, so an adversary that asks
only such pairs has advantage `0` even against the revealing puzzle.

A last check pins down that the challenger's encryptions share the adversary's oracle: a DEM that
masks with the answer `H ()`, a puzzle whose key is `H ()`, and an adversary that reads `H ()` in
preprocessing and in one online round recover the hidden bit with advantage `1`. Were the
challenger's queries answered from a cache of its own, the mask would be an independent uniform
bit and the advantage `0`.
-/

public section

open OracleComp OracleSpec ENNReal MeasureTheory TimeLockPuzzle

namespace VCVioTest.TimeLockPuzzle.Hiding

/-- One random bit: the oracle `H : Unit → Bool`. -/
abbrev keySpec : OracleSpec Unit := Unit →ₒ Bool

/-- The puzzle that reveals its key: one round asking `H ()`, whose answer is both the puzzle and
the key. -/
def reveal : TimeLockPuzzle keySpec Bool Bool where
  gen := do
    let k ← queryPoint ()
    pure (k, k)
  solve z := pure (some z)

/-- The one-bit pad over the puzzle's oracles, under a one-bit key. The hiding game keys its DEM
by the puzzle together with its key, and `pad.comap Prod.snd` is the pad that ignores the
puzzle. -/
def pad : DEMScheme (OracleComp (unifSpec + keySpec)) Bool Bool Bool where
  encrypt k msg := pure (k ^^ msg)
  decrypt k c := pure (k ^^ c)

/-- The free oracles of a hiding adversary on bits: local coins and the challenge oracle. -/
abbrev freeSpec : OracleSpec (ℕ ⊕ (Bool × Bool)) := unifSpec + LeftOrRight.spec Bool Bool

/-- The adversary that decrypts with the revealed key: no preprocessing, one challenge query on
`(false, true)`, and the pad decryption of the answer under the puzzle as its guess. -/
def decryptAdv : HidingAdversary keySpec Bool Bool Bool where
  State := Unit
  preprocess := pure ()
  online _ z := do
    let c? : Option Bool ← liftM ((freeSpec + keySpec.batch).query (.inl (.inr (false, true))))
    pure (z ^^ c?.getD false)

/-- It makes no preprocessing query and submits no round. -/
theorem decryptAdv_isQueryBound : decryptAdv.IsQueryBound 0 (0, 0) :=
  ⟨by simp [decryptAdv], fun _ _ => by simp [decryptAdv]⟩

/-- It makes one challenge query. -/
theorem decryptAdv_makesAtMostQueries : decryptAdv.MakesAtMostQueries 1 := fun _ _ => by
  simp [decryptAdv]

/-- No challenge query is not enough. -/
example : ¬ decryptAdv.MakesAtMostQueries 0 := fun h => by
  simpa [decryptAdv] using h () true

/-- Against any fixed answer table for `H`, the decrypting adversary's guess is the hidden bit. -/
lemma simulateQ_hidingExperiment_decryptAdv (f : QueryImpl keySpec Id) (b : Bool) :
    simulateQ (unifFwdAnswerImpl f)
        (reveal.hidingExperiment (pad.comap Prod.snd) (fun _ => ()) decryptAdv b) =
      pure b := by
  simp [hidingExperiment, decryptAdv, reveal, pad, QueryImpl.simulateQ_simulateQ_unbatch]

/-- In the random oracle model the decrypting adversary's guess is the hidden bit with
probability `1`. -/
lemma rom_evalDist_hidingExperiment_decryptAdv (b : Bool) :
    (ProbCompRuntime.rom keySpec).evalDist
      (reveal.hidingExperiment (pad.comap Prod.snd) (fun _ => ()) decryptAdv b) {b} = 1 := by
  rw [ProbCompRuntime.rom_evalDist, ← Set.ofPred_eq_eq_singleton,
    evalDist_apply_setOf_simulateQ_romImpl_run'_eq_one_iff]
  intro f _
  simp [simulateQ_hidingExperiment_decryptAdv]

/-- A revealed key decrypts the challenge: the decrypting adversary has hiding advantage `1`. -/
theorem hidingAdvantage_decryptAdv :
    hidingAdvantage reveal (pad.comap Prod.snd) (fun _ => ()) decryptAdv = 1 := by
  set μ := fun b => (ProbCompRuntime.rom keySpec).evalDist
    (reveal.hidingExperiment (pad.comap Prod.snd) (fun _ => ()) decryptAdv b)
  have h₁ : μ true {true} = 1 := rom_evalDist_hidingExperiment_decryptAdv true
  have h₀ : μ false {true} = 0 := by
    have hsum := Measure.apply_true_add_apply_false (μ false)
    rw [rom_evalDist_hidingExperiment_decryptAdv false] at hsum
    have hle : μ false {true} + 1 ≤ 0 + 1 := by
      rw [hsum, zero_add]
      exact ProbCompRuntime.evalDist_apply_univ_le_one _ _
    exact le_antisymm ((ENNReal.add_le_add_iff_right one_ne_top).1 hle) zero_le
  rw [hidingAdvantage_eq]
  change ENNReal.absDiff (μ true {true}) (μ false {true}) = 1
  rw [h₁, h₀]
  simp [ENNReal.absDiff]

/-- The revealing puzzle is not hiding at any bound below `1`, even against adversaries with no
preprocessing query, no round and one challenge query. -/
theorem not_hidingSecure_reveal {ε : ℝ≥0∞} (hε : ε < 1) :
    ¬ HidingSecure reveal (pad.comap Prod.snd) (fun _ => ()) 0 (0, 0) 1 ε := fun h =>
  (h decryptAdv decryptAdv_isQueryBound decryptAdv_makesAtMostQueries).not_gt
    (hidingAdvantage_decryptAdv ▸ hε)

/-! ## An adversary that ignores the challenge -/

/-- The adversary that outputs `true` without querying anything. -/
def constAdv : HidingAdversary keySpec Bool Bool Bool := ⟨Unit, pure (), fun _ _ => pure true⟩

theorem constAdv_isQueryBound : constAdv.IsQueryBound 0 (0, 0) :=
  ⟨by simp [constAdv], fun _ _ => by simp [constAdv]⟩

theorem constAdv_makesAtMostQueries : constAdv.MakesAtMostQueries 0 := fun _ _ => by
  simp [constAdv]

/-- The constant adversary has hiding advantage `0`. -/
theorem hidingAdvantage_constAdv :
    hidingAdvantage reveal (pad.comap Prod.snd) (fun _ => ()) constAdv = 0 := by
  have h : reveal.hidingExperiment (pad.comap Prod.snd) (fun _ => ()) constAdv true =
      reveal.hidingExperiment (pad.comap Prod.snd) (fun _ => ()) constAdv false := by
    simp [hidingExperiment, constAdv]
  rw [hidingAdvantage_eq, h, ENNReal.absDiff_self]

/-! ## Length leakage -/

/-- The pad extended to lists of bits under a one-bit key. -/
def listPad : DEMScheme (OracleComp (unifSpec + keySpec)) Bool (List Bool) (List Bool) where
  encrypt k msg := pure (msg.map (k ^^ ·))
  decrypt k c := pure (c.map (k ^^ ·))

/-- The adversary that asks the inadmissible pair `([], [true])`, whose lengths differ, and would
decrypt the answer with the revealed key. -/
def lengthAdv : HidingAdversary keySpec Bool (List Bool) (List Bool) where
  State := Unit
  preprocess := pure ()
  online _ z := do
    let c? : Option (List Bool) ← liftM
      (((unifSpec + LeftOrRight.spec (List Bool) (List Bool)) + keySpec.batch).query
        (.inl (.inr ([], [true]))))
    pure ((c?.map (·.map (z ^^ ·))) == some [true])

theorem lengthAdv_makesAtMostQueries : lengthAdv.MakesAtMostQueries 1 := fun _ _ => by
  simp [lengthAdv]

/-- The pair is refused at both hidden bits, so the adversary's view does not depend on the bit:
its hiding advantage under the length leakage is `0`. -/
theorem hidingAdvantage_lengthAdv :
    hidingAdvantage reveal (listPad.comap Prod.snd) List.length lengthAdv = 0 := by
  have h : reveal.hidingExperiment (listPad.comap Prod.snd) List.length lengthAdv true =
      reveal.hidingExperiment (listPad.comap Prod.snd) List.length lengthAdv false := by
    simp [hidingExperiment, lengthAdv]
  rw [hidingAdvantage_eq, h, ENNReal.absDiff_self]

/-- Without leakage the same pair is admissible, and the adversary recovers the hidden bit's
message. -/
lemma simulateQ_hidingExperiment_lengthAdv_unit (f : QueryImpl keySpec Id) (b : Bool) :
    simulateQ (unifFwdAnswerImpl f)
        (reveal.hidingExperiment (listPad.comap Prod.snd) (fun _ => ()) lengthAdv b) =
      pure b := by
  cases b <;> simp [hidingExperiment, lengthAdv, reveal, listPad,
    QueryImpl.simulateQ_simulateQ_unbatch]

/-! ## One oracle for the adversary and the challenger -/

/-- A puzzle that reveals nothing, whose key is the answer `H ()` asked in one round. -/
def hidden : TimeLockPuzzle keySpec Unit Bool where
  gen := do
    let k ← queryPoint ()
    pure ((), k)
  solve _ := (fun k => some k) <$> queryPoint ()

/-- A DEM keyed by the puzzle with its key whose encryption masks the message with the key and
with its own query `H ()`. -/
def maskDEM : DEMScheme (OracleComp (unifSpec + keySpec)) (Unit × Bool) Bool Bool where
  encrypt pk msg := do
    let h ← liftM ((unifSpec + keySpec).query (.inr ()))
    pure (h ^^ pk.2 ^^ msg)
  decrypt pk c := do
    let h ← liftM ((unifSpec + keySpec).query (.inr ()))
    pure (h ^^ pk.2 ^^ c)

/-- The adversary that reads `H ()` in preprocessing, asks for the encryption of `false` or
`true`, reads `H ()` again in an online round, and removes from the ciphertext the three masks
it expects. -/
def sharedAdv : HidingAdversary keySpec Unit Bool Bool where
  State := Bool
  preprocess := liftM ((unifSpec + keySpec).query (.inr ()))
  online h₀ _ := do
    let c? : Option Bool ← liftM ((freeSpec + keySpec.batch).query (.inl (.inr (false, true))))
    let us ← liftM ((freeSpec + keySpec.batch).query (.inr [()]))
    pure (c?.getD false ^^ h₀ ^^ us ⟨0, Nat.zero_lt_one⟩)

/-- It makes one preprocessing query and submits one round of one point. -/
theorem sharedAdv_isQueryBound : sharedAdv.IsQueryBound 1 (1, 1) :=
  ⟨by simp [sharedAdv], fun _ _ => by simp [sharedAdv]⟩

/-- It makes one challenge query. -/
theorem sharedAdv_makesAtMostQueries : sharedAdv.MakesAtMostQueries 1 := fun _ _ => by
  simp [sharedAdv]

/-- A fixed answer table answers a query to `H` with its entry. -/
lemma unifFwdAnswerImpl_apply_inr (f : QueryImpl keySpec Id) (t : Unit) :
    unifFwdAnswerImpl f (.inr t) = (pure (f t).run : ProbComp Bool) := rfl

/-- A query to `H` lifted from `keySpec` is answered by the table's entry. -/
@[simp]
lemma simulateQ_unifFwdAnswerImpl_liftM_query (f : QueryImpl keySpec Id) (t : Unit) :
    simulateQ (unifFwdAnswerImpl f)
        (liftM (liftM (keySpec.query t) : OracleComp keySpec Bool) :
          OracleComp (unifSpec + keySpec) Bool) = pure (f t).run := by
  rw [← OracleComp.liftComp_eq_liftM, OracleComp.liftComp_liftM_query, unifFwdAnswerImpl,
    QueryImpl.passthrough_add, QueryImpl.simulateQ_add_liftM_query_right]
  rfl

/-- The answer at the first point of a round is the answer to that point. -/
@[simp]
lemma batchCons_mk_zero {t : Unit} {ts : List Unit} (u : keySpec.Range t)
    (us : keySpec.batch.Range ts) (h : 0 < (t :: ts).length) : batchCons u us ⟨0, h⟩ = u := rfl

/-- Against any fixed answer table for `H`, the four reads of `H ()` (the adversary's two, the
generator's and the challenger's) agree, and the guess is the hidden bit. -/
lemma simulateQ_hidingExperiment_sharedAdv (f : QueryImpl keySpec Id) (b : Bool) :
    simulateQ (unifFwdAnswerImpl f) (hidden.hidingExperiment maskDEM (fun _ => ()) sharedAdv b) =
      pure b := by
  simp [hidingExperiment, sharedAdv, hidden, maskDEM, QueryImpl.simulateQ_simulateQ_unbatch,
    unifFwdAnswerImpl_apply_inr]

/-- In the random oracle model the guess is the hidden bit with probability `1`. -/
lemma rom_evalDist_hidingExperiment_sharedAdv (b : Bool) :
    (ProbCompRuntime.rom keySpec).evalDist
      (hidden.hidingExperiment maskDEM (fun _ => ()) sharedAdv b) {b} = 1 := by
  rw [ProbCompRuntime.rom_evalDist, ← Set.ofPred_eq_eq_singleton,
    evalDist_apply_setOf_simulateQ_romImpl_run'_eq_one_iff]
  intro f _
  simp [simulateQ_hidingExperiment_sharedAdv]

/-- The challenger's encryptions query the adversary's oracle: the adversary has hiding advantage
`1`. -/
theorem hidingAdvantage_sharedAdv : hidingAdvantage hidden maskDEM (fun _ => ()) sharedAdv = 1 := by
  set μ := fun b => (ProbCompRuntime.rom keySpec).evalDist
    (hidden.hidingExperiment maskDEM (fun _ => ()) sharedAdv b)
  have h₁ : μ true {true} = 1 := rom_evalDist_hidingExperiment_sharedAdv true
  have h₀ : μ false {true} = 0 := by
    have hsum := Measure.apply_true_add_apply_false (μ false)
    rw [rom_evalDist_hidingExperiment_sharedAdv false] at hsum
    have hle : μ false {true} + 1 ≤ 0 + 1 := by
      rw [hsum, zero_add]
      exact ProbCompRuntime.evalDist_apply_univ_le_one _ _
    exact le_antisymm ((ENNReal.add_le_add_iff_right one_ne_top).1 hle) zero_le
  rw [hidingAdvantage_eq]
  change ENNReal.absDiff (μ true {true}) (μ false {true}) = 1
  rw [h₁, h₀]
  simp [ENNReal.absDiff]

/-- So the masking DEM is not hiding at any bound below `1` against adversaries with one
preprocessing query, one round of one point and one challenge query. -/
theorem not_hidingSecure_maskDEM {ε : ℝ≥0∞} (hε : ε < 1) :
    ¬ HidingSecure hidden maskDEM (fun _ => ()) 1 (1, 1) 1 ε := fun h =>
  (h sharedAdv sharedAdv_isQueryBound sharedAdv_makesAtMostQueries).not_gt
    (hidingAdvantage_sharedAdv ▸ hε)

end VCVioTest.TimeLockPuzzle.Hiding
