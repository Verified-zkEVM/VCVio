/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.Schemes.PointerChainPuzzle.LeanSealHidingBridge

/-!
# The hiding adversary adapter and the hiding-experiment comparison: checks

A toy encoding of the typed oracle `ℕ →ₒ Fin 8` into the raw oracle `ℕ →ₒ Fin 8`: the typed
point `t` at the raw input `2 * t`, odd raw inputs encoding no typed point. A raw adversary over the
hiding adversary's free summand, local coins and the left-or-right challenge oracle, queries the
odd input `5` in preprocessing; online, it asks the challenge `(3, 4)` and submits the raw round
`[2, 5, 2, 5]`.

Run deterministically, with local coins read off a counter, the adapted adversary forwards the
challenge once, submits exactly one typed round `[1, 1]`, with the repeated point kept, and
answers both occurrences of `5` with the value drawn in preprocessing. Its online budget is
`(1, 2)` where the raw adversary's is `(1, 4)`, and the encryption budget `1` carries over. The
coin lift into the free summand lands on the coin summand, so private draws are never challenge
queries.

On the same encoding, a toy DEM whose ciphertext is the answer at the typed point `1` (at the raw
input `2` in the raw world) is checked against raw adversaries that also read the answer at `2`:
with the challenge first, with their own query first, and with their query cached in
preprocessing, they win the raw hiding experiment with probability one, and by the comparison
theorem so do their adapted adversaries in the typed experiment. The comparison is also
instantiated at the byte encoding of leanSeal, with a DEM that makes no oracle queries.
-/

public section

open OracleComp OracleSpec TimeLockPuzzle

namespace VCVioTest.LeanSealHidingBridge

/-! ## The coin lift -/

/-- The coin lift into the hiding adversary's free summand lands on the coin summand. -/
example {Msg C : Type} (k : ℕ) :
    (liftM (unifSpec.query k) : OracleQuery (unifSpec + LeftOrRight.spec Msg C) (Fin (k + 1))) =
      (unifSpec + LeftOrRight.spec Msg C).query (.inl k) := rfl

/-! ## A toy encoding -/

/-- The typed oracle. -/
abbrev typSpec : OracleSpec ℕ := ℕ →ₒ Fin 8

/-- The raw oracle. -/
abbrev rawSpec : OracleSpec ℕ := ℕ →ₒ Fin 8

/-- The typed point `t` at the raw input `2 * t`; an odd raw input encodes no typed point. Typed
answers are whole raw values. -/
@[expose]
noncomputable def toyEnc : RandomOracleEncoding typSpec ℕ (Fin 8) :=
  .ofSplit (Tail := fun _ => Unit) (fun t => 2 * t)
    (fun x => if x % 2 = 0 then some (x / 2) else none)
    (by
      intro x t h
      split_ifs at h with hx
      cases h
      omega)
    (fun t => by simp) (fun _ => (Equiv.prodPUnit _).symm)

/-- The raw round: the encoding `2` of the typed point `1` twice, and the odd input `5` twice. -/
abbrev rawRound : List ℕ := [2, 5, 2, 5]

/-- Its inputs that encode typed points: the typed round `[1, 1]`. -/
example : rawRound.filterMap toyEnc.route = [1, 1] := by decide

/-! ## The raw adversary and its adaptation -/

/-- The free summand of hiding adversaries with messages and ciphertexts in `ℕ`. -/
abbrev freeSpec : OracleSpec (ℕ ⊕ ℕ × ℕ) := unifSpec + LeftOrRight.spec ℕ ℕ

/-- Preprocessing queries the odd input `5` and keeps its answer; online, the adversary asks the
challenge `(3, 4)`, submits the raw round, and returns the challenge answer with the kept answer
followed by the round's answers. -/
@[expose]
def srcAdv : TwoPhaseAdversary freeSpec rawSpec Unit (Option ℕ × List ℕ) where
  State := Fin 8
  preprocess := liftM ((unifSpec + rawSpec).query (.inr 5))
  online v _ := do
    let c ← (liftM ((freeSpec + rawSpec.batch).query (.inl (.inr (3, 4)))) :
      OracleComp (freeSpec + rawSpec.batch) (Option ℕ))
    let us ← liftM ((freeSpec + rawSpec.batch).query (.inr rawRound))
    pure (c, v.val :: List.ofFn fun j => (us j : Fin 8).val)

/-- Local coins read off a counter, which then moves on. -/
def counterCoins {σ : Type} (get : σ → ℕ) (set : ℕ → σ → σ) : QueryImpl unifSpec (StateT σ Id) :=
  fun n => StateT.mk fun s => pure (⟨get s % (n + 1), Nat.mod_lt _ n.succ_pos⟩, set (get s + 1) s)

/-- The typed oracle `t ↦ t + 5 mod 8`. -/
def typAnswer (t : ℕ) : Fin 8 := ⟨(t + 5) % 8, Nat.mod_lt _ (by decide)⟩

/-- The preprocessing oracles: coins from the counter, and the typed oracle. -/
def preImpl : QueryImpl (unifSpec + typSpec) (StateT ℕ Id) :=
  counterCoins id (fun k _ => k) +
    (fun t => pure (typAnswer t) : QueryImpl typSpec (StateT ℕ Id))

/-- The online state: the coin counter, the typed rounds and the challenges, latest first. -/
abbrev OnState := ℕ × List (List ℕ) × List (ℕ × ℕ)

/-- Challenges answered by `(m₀, m₁) ↦ 10 m₀ + m₁` and recorded in the log. -/
def challenges : QueryImpl (LeftOrRight.spec ℕ ℕ) (StateT OnState Id) :=
  fun mm => StateT.mk fun s => pure (some (10 * mm.1 + mm.2), (s.1, s.2.1, mm :: s.2.2))

/-- Typed rounds answered by the typed oracle and recorded in the log. -/
def typRounds : QueryImpl typSpec.batch (StateT OnState Id) :=
  fun ts => StateT.mk fun s =>
    pure ((fun j => typAnswer ts[j] : typSpec.batch.Range ts), (s.1, ts :: s.2.1, s.2.2))

/-- The online oracles: coins from the counter, challenges, and typed rounds. -/
def onImpl : QueryImpl (freeSpec + typSpec.batch) (StateT OnState Id) :=
  (counterCoins (σ := OnState) Prod.fst (fun k s => (k, s.2)) + challenges) + typRounds

/-- Run the adapted adversary from coin counter `3`: preprocessing, then the online phase on its
state; return the output, the typed rounds and the challenges, in order. -/
noncomputable def runAdapted : (Option ℕ × List ℕ) × List (List ℕ) × List (ℕ × ℕ) :=
  let adv := toyEnc.adaptTwoPhase srcAdv
  let (σ, k) := ((simulateQ preImpl adv.preprocess).run 3).run
  let (out, _, rounds, chals) := ((simulateQ onImpl (adv.online σ ())).run (k, [], [])).run
  (out, rounds.reverse, chals.reverse)

/-- The challenge is forwarded once and answered `34`. One typed round `[1, 1]` is submitted, with
the repeated point kept, and both occurrences of `2` get the typed answer `6` there. Preprocessing
draws `3` at the odd input `5`, and both occurrences of `5` get `3` from the private cache. -/
theorem runAdapted_eq : runAdapted = ((some 34, [3, 6, 3, 6, 3]), [[1, 1]], [(3, 4)]) := by
  decide

/-! ## Budgets -/

/-- The raw adversary makes one preprocessing query and submits one round of four inputs. -/
theorem srcAdv_isQueryBound : srcAdv.IsQueryBound 1 (1, 4) := by
  refine ⟨by simp [srcAdv], fun v _ => ?_⟩
  simp [srcAdv, IsOnlineQueryBound]

/-- The adapter keeps the budget. -/
example : (toyEnc.adaptTwoPhase srcAdv).IsQueryBound 1 (1, 4) :=
  toyEnc.isQueryBound_adaptTwoPhase srcAdv_isQueryBound

/-- The typed round holds only the two typed points: the online budget is `(1, 2)`. -/
theorem adaptTwoPhase_srcAdv_isQueryBound :
    (toyEnc.adaptTwoPhase srcAdv).IsQueryBound 1 (1, 2) := by
  refine ⟨(toyEnc.isQueryBound_adaptTwoPhase srcAdv_isQueryBound).1, fun σ _ => ?_⟩
  simp only [RandomOracleEncoding.adaptTwoPhase, srcAdv, simulateQ_bind, simulateQ_spec_query,
    simulateQ_pure, StateT.run'_eq, StateT.run_bind, StateT.run_pure, map_bind]
  refine isOnlineQueryBound_bind_le (0, 0) (1, 2) ?_ (fun z => ?_) ⟨by omega, by omega⟩
  · exact (toyEnc.isOnlineQueryBound_freeOnlineImpl _ _).mono le_rfl
  · refine isOnlineQueryBound_bind_le (1, 2) (0, 0) ?_ (fun _ => ?_) ⟨le_rfl, le_rfl⟩
    · exact toyEnc.isOnlineQueryBound_freeOnlineImpl_inr_run rawRound z.2
    · simp [IsOnlineQueryBound]

/-- The hiding adversary of `srcAdv`: it guesses `true` when its challenge is answered. -/
@[expose]
def hideAdv : HidingAdversary rawSpec Unit ℕ ℕ := srcAdv.mapOutput fun out => out.1.isSome

/-- It makes one challenge query. -/
theorem hideAdv_makesAtMostQueries : hideAdv.MakesAtMostQueries 1 := by
  intro v _
  simp [hideAdv, TwoPhaseAdversary.mapOutput, srcAdv]

/-- The hiding adapter keeps the encryption budget. -/
example : (toyEnc.adaptHidingAdversary hideAdv).MakesAtMostQueries 1 :=
  toyEnc.makesAtMostQueries_adaptHidingAdversary hideAdv_makesAtMostQueries

/-! ## The hiding experiments: a challenger and an adversary on one oracle

A toy puzzle with constant puzzle and key, and a toy DEM whose encryption returns the answer at
the typed point `1`; its raw counterpart queries `2`, which encodes `1`. Each raw adversary also
reads the answer at `2`, and wins when it equals the challenge ciphertext: with the challenge
first, with its own query first, and with its query cached in preprocessing. In the raw world it
wins with probability one, and by the comparison theorem so does its adapted adversary in the
typed world: the challenger and the adapter share the typed oracle's cache. -/

/-- The free summand of these hiding adversaries. -/
abbrev chalSpec : OracleSpec (ℕ ⊕ (Unit × Unit)) := unifSpec + LeftOrRight.spec Unit (Fin 8)

/-- The raw toy puzzle: a constant puzzle and key. -/
def tlpRaw : TimeLockPuzzle rawSpec Unit Unit where
  gen := pure ((), ())
  solve _ := pure (some ())

/-- The typed toy puzzle: a constant puzzle and key. -/
def tlpTyp : TimeLockPuzzle typSpec Unit Unit where
  gen := pure ((), ())
  solve _ := pure (some ())

/-- The raw toy DEM: the ciphertext is the answer at the raw input `2`. -/
def demRaw : DEMScheme (OracleComp (unifSpec + rawSpec)) (Unit × Unit) Unit (Fin 8) where
  encrypt _ _ := liftM ((unifSpec + rawSpec).query (.inr 2))
  decrypt _ _ := pure ()

/-- The typed toy DEM: the ciphertext is the answer at the typed point `1`. -/
def demTyp : DEMScheme (OracleComp (unifSpec + typSpec)) (Unit × Unit) Unit (Fin 8) where
  encrypt _ _ := liftM ((unifSpec + typSpec).query (.inr 1))
  decrypt _ _ := pure ()

/-- The challenge first, then the round `[2]`. -/
def advChalFirst : HidingAdversary rawSpec Unit Unit (Fin 8) where
  State := Unit
  preprocess := pure ()
  online _ _ := do
    let c ← (liftM ((chalSpec + rawSpec.batch).query (.inl (.inr ((), ())))) :
      OracleComp (chalSpec + rawSpec.batch) (Option (Fin 8)))
    let us ← liftM ((chalSpec + rawSpec.batch).query (.inr [2]))
    pure (decide (c = some (us ⟨0, by simp⟩)))

/-- The round `[2]` first, then the challenge. -/
def advRoundFirst : HidingAdversary rawSpec Unit Unit (Fin 8) where
  State := Unit
  preprocess := pure ()
  online _ _ := do
    let us ← liftM ((chalSpec + rawSpec.batch).query (.inr [2]))
    let c ← (liftM ((chalSpec + rawSpec.batch).query (.inl (.inr ((), ())))) :
      OracleComp (chalSpec + rawSpec.batch) (Option (Fin 8)))
    pure (decide (c = some (us ⟨0, by simp⟩)))

/-- The input `2` queried in preprocessing, then the challenge online. -/
def advPreprocess : HidingAdversary rawSpec Unit Unit (Fin 8) where
  State := Fin 8
  preprocess := liftM ((unifSpec + rawSpec).query (.inr 2))
  online σ _ := do
    let c ← (liftM ((chalSpec + rawSpec.batch).query (.inl (.inr ((), ())))) :
      OracleComp (chalSpec + rawSpec.batch) (Option (Fin 8)))
    pure (decide (c = some σ))

/-- The raw generator is the typed one with its rounds encoded. -/
theorem tlpRaw_gen : tlpRaw.gen = simulateQ toyEnc.roundImpl tlpTyp.gen := by
  simp [tlpRaw, tlpTyp]

/-- The raw encryption is the typed one with its query encoded. -/
theorem demRaw_encrypt (key : Unit × Unit) (msg : Unit) :
    demRaw.encrypt key msg =
      simulateQ (toyEnc.encodeImpl ∘ₛ RandomOracleEncoding.typedLift) (demTyp.encrypt key msg) := by
  simp [demRaw, demTyp, RandomOracleEncoding.typedLift, RandomOracleEncoding.encodeImpl, toyEnc,
    RandomOracleEncoding.ofSplit]

/-- The toy encoding is injective, so it never clashes. -/
theorem toyEnc_not_clash (c : typSpec.QueryCache) : ¬ toyEnc.Clash c := by
  rintro ⟨q, q', hne, -, -, he⟩
  exact hne (by simpa [toyEnc, RandomOracleEncoding.ofSplit] using he)

/-- With the challenge first, the raw adversary wins with probability one. -/
theorem advChalFirst_raw (b : Bool) :
    (ProbCompRuntime.rom rawSpec).evalDist
      (tlpRaw.hidingExperiment demRaw (fun _ => ()) advChalFirst b) {true} = 1 := by
  rw [ProbCompRuntime.rom_evalDist, ← prEvent_eq_evalDist_singleton]
  simp [hidingExperiment, tlpRaw, advChalFirst, demRaw, StateT.run'_eq,
    QueryImpl.simulateQ_add_liftM_right]

/-- With its own query first, the raw adversary wins with probability one. -/
theorem advRoundFirst_raw (b : Bool) :
    (ProbCompRuntime.rom rawSpec).evalDist
      (tlpRaw.hidingExperiment demRaw (fun _ => ()) advRoundFirst b) {true} = 1 := by
  rw [ProbCompRuntime.rom_evalDist, ← prEvent_eq_evalDist_singleton]
  simp [hidingExperiment, tlpRaw, advRoundFirst, demRaw, StateT.run'_eq,
    QueryImpl.simulateQ_add_liftM_right]

/-- With its query cached in preprocessing, the raw adversary wins with probability one. -/
theorem advPreprocess_raw (b : Bool) :
    (ProbCompRuntime.rom rawSpec).evalDist
      (tlpRaw.hidingExperiment demRaw (fun _ => ()) advPreprocess b) {true} = 1 := by
  rw [ProbCompRuntime.rom_evalDist, ← prEvent_eq_evalDist_singleton]
  simp [hidingExperiment, tlpRaw, advPreprocess, demRaw, StateT.run'_eq]

/-- With the challenge first, the adapted adversary wins the typed experiment with probability
one. -/
theorem advChalFirst_typed (b : Bool) :
    (ProbCompRuntime.rom typSpec).evalDist (tlpTyp.hidingExperiment demTyp (fun _ => ())
      (toyEnc.adaptHidingAdversary advChalFirst) b) {true} = 1 := by
  rw [← toyEnc.evalDist_hidingExperiment_adaptHidingAdversary _ tlpRaw_gen demRaw_encrypt
    toyEnc_not_clash]
  exact advChalFirst_raw b

/-- With its own query first, the adapted adversary wins the typed experiment with probability
one. -/
theorem advRoundFirst_typed (b : Bool) :
    (ProbCompRuntime.rom typSpec).evalDist (tlpTyp.hidingExperiment demTyp (fun _ => ())
      (toyEnc.adaptHidingAdversary advRoundFirst) b) {true} = 1 := by
  rw [← toyEnc.evalDist_hidingExperiment_adaptHidingAdversary _ tlpRaw_gen demRaw_encrypt
    toyEnc_not_clash]
  exact advRoundFirst_raw b

/-- With its query cached in preprocessing, the adapted adversary wins the typed experiment with
probability one: the adapter's preprocessing caches the typed point `1` in the typed oracle, which
the challenger then reads. -/
theorem advPreprocess_typed (b : Bool) :
    (ProbCompRuntime.rom typSpec).evalDist (tlpTyp.hidingExperiment demTyp (fun _ => ())
      (toyEnc.adaptHidingAdversary advPreprocess) b) {true} = 1 := by
  rw [← toyEnc.evalDist_hidingExperiment_adaptHidingAdversary _ tlpRaw_gen demRaw_encrypt
    toyEnc_not_clash]
  exact advPreprocess_raw b

/-- The hiding advantages agree: here both are zero, the adversary winning at both hidden bits. -/
example : hidingAdvantage tlpRaw demRaw (fun _ => ()) advChalFirst =
    hidingAdvantage tlpTyp demTyp (fun _ => ()) (toyEnc.adaptHidingAdversary advChalFirst) :=
  toyEnc.hidingAdvantage_eq_hidingAdvantage_adaptHidingAdversary _ tlpRaw_gen demRaw_encrypt
    toyEnc_not_clash advChalFirst

end VCVioTest.LeanSealHidingBridge

/-! ## The leanSeal instance -/

namespace VCVioTest.LeanSealHidingBridge.Byte

open PointerChainPuzzle.LeanSeal

/-- A DEM that makes no oracle queries: the ciphertext is the message. -/
def plainDem {ι : Type} (spec : OracleSpec ι) (b n : ℕ) :
    DEMScheme (OracleComp (unifSpec + spec)) (Puzzle b n × Bytes 32) Bool Bool where
  encrypt _ msg := pure msg
  decrypt _ c := pure c

/-- The comparison at the byte encoding of leanSeal: the generator refinement is `roundImpl_eq`,
and a DEM that makes no oracle queries refines itself. -/
example {b n : ℕ} (hb : b ≤ 32) (hn : n < 2 ^ 32) (m : ℕ) [NeZero n]
    (adv : HidingAdversary byteSpec (Puzzle b n) Bool Bool) :
    hidingAdvantage (byteScheme b n m) (plainDem byteSpec b n) (fun _ => ()) adv =
      hidingAdvantage (typedScheme b n m) (plainDem (typedSpec b n) b n) (fun _ => ())
        ((encoding hb hn).adaptHidingAdversary adv) :=
  (encoding hb hn).hidingAdvantage_eq_hidingAdvantage_adaptHidingAdversary _
    (by rw [byteScheme, roundImpl_eq hb hn]; rfl) (fun _ _ => by simp [plainDem])
    (not_clash hb hn) adv

end VCVioTest.LeanSealHidingBridge.Byte
