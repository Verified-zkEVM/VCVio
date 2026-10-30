/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.Schemes.PointerChainPuzzle.HidingNonce

/-!
# Time-lock encryption with the pointer-chain puzzle: checks of the nonce hop

Checks through the public API, for two chains of one step (`n = 2`, `m = 1`) over `S = Fin 11`,
`L = Fin 5`, `Salt = Ctx = Fin 3`, nonces `N = Fin 4` with a one-byte codec, PRF keys `K = Fin 7`
and a toy PRF:

* traces of the challengers on a tape of local coins, where the coin query `n` takes the head of the
  tape modulo `n + 1`: two accepted encryptions that draw the same nonce get the subkeys of two
  separate draws from the counter-indexed challenger of `G₁½`, which logs both with that nonce,
  and the same subkeys from the private challenger of `G₁`, which reads the second pair from its
  cache (the countermodel for per-encryption keys before the nonce hop);
* a pair of messages of unequal length leaves the counter of `G₁½` unchanged and draws no coin, in
  the challenger and in the joint handler of the online phase; an accepted pair beyond the budget
  advances the counter and draws no coin;
* the main theorems applied at a concrete hiding adversary with one challenge query: `G₁` and `G₁½`
  agree at budget `1`, `G₁½` is `G₂` in law, and `|G₁ - G₂| ≤ 1 / 8`. Its guess reads the first
  byte of the envelope, which is the first byte of the header, so these are checks of the API only;
* an adversary that asks two identical challenges and guesses whether the two envelopes are equal
  separates the hybrids through the experiments: equality has probability exactly `1 / 4` in `G₁`,
  where it is a nonce collision, and exactly `1 / 196` in `G₁½` at budget `2`, where the subkeys
  must collide too. The toy envelope of a one-byte message determines its nonce and its subkeys. The
  gap `12 / 49` is within the bound `1 / 4` of the nonce hop at budget `2`.

The answer types are sampled through `SampleableType.Fin`, so loading this module enumerates no
type.
-/

public section

open OracleComp OracleSpec PointerChainPuzzle PointerChainPuzzle.LeanSeal
  PointerChainPuzzle.LeanSeal.Envelope PRFScheme
open scoped ENNReal

namespace VCVioTest.PointerChainPuzzle.HidingNonce

/-- States are `Fin 11`. -/
abbrev S := Fin 11

/-- Links are `Fin 5`. -/
abbrev L := Fin 5

/-- Salts and contexts are `Fin 3`. -/
abbrev Salt := Fin 3

/-- Nonces are `Fin 4`. -/
abbrev N := Fin 4

/-- PRF keys are `Fin 7`. -/
abbrev K := Fin 7

/-- The oracles with subkeys at these parameters. -/
abbrev spec := sealSpec 2 S L Salt Salt N K

/-- Nonces are encoded as one byte. -/
@[expose]
def codec : FixedCodec N 1 where
  encode x := ⟨#v[x.val.toUInt8]⟩
  decode y := if h : y.toVector[0].toNat < 4 then some ⟨_, h⟩ else none
  decode_encode x := by fin_cases x <;> rfl

/-- A toy PRF: byte `i` of `eval k x` is `k + |x| + x₀ + i`, with `x₀` the first byte of `x`. -/
@[expose]
def toyPRF : PRFScheme K ByteArray (Bytes 32) where
  keygen := $ᵗ K
  eval k x :=
    ⟨Vector.ofFn fun i => (k.val + x.size + (x.data.toList.headD 0).toNat + i.val).toUInt8⟩

/-- The toy PRF draws its key uniformly. -/
theorem toyPRF_uniformKey : toyPRF.UniformKey :=
  rfl

/-- The puzzle bytes `[7, 7]`. -/
@[expose]
def pz : ByteArray := ⟨#[7, 7]⟩

/-- The one-byte message `[1]`. -/
@[expose]
def msgA : Plaintext := ⟨⟨#[1]⟩, by decide⟩

/-- The one-byte message `[2]`. -/
@[expose]
def msgB : Plaintext := ⟨⟨#[2]⟩, by decide⟩

/-- The two-byte message `[1, 2]`. -/
@[expose]
def msgC : Plaintext := ⟨⟨#[1, 2]⟩, by decide⟩

/-! ## Traces on a tape of local coins -/

/-- Local coins from a tape: the coin query `n` is answered with the head of the tape modulo
`n + 1`, which is dropped; rounds are answered from the table `g`. -/
@[expose]
def tapeImpl (g : QueryImpl spec Id) : QueryImpl (unifSpec + spec.batch) (StateM (List ℕ))
  | .inl n => do
      let l ← get
      set l.tail
      pure ⟨l.headD 0 % (n + 1), Nat.mod_lt _ n.succ_pos⟩
  | .inr ts => pure (g.batch ts)

/-- Two challenge queries on the pair `mm` to the left-or-right oracle over `enc` at hidden bit
`b`, from the state `s`, run on the tape `tape`: the two answers, the final state and the rest of
the tape. -/
@[expose]
def twoChallenges {σ : Type} (g : QueryImpl spec Id)
    (enc : Plaintext → StateT σ (OracleComp (unifSpec + spec.batch)) ByteArray) (b : Bool)
    (mm : Plaintext × Plaintext) (s : σ) (tape : List ℕ) :
    ((Option ByteArray × Option ByteArray) × σ) × List ℕ :=
  (simulateQ (tapeImpl g) ((do
    let c₁ ← LeftOrRight.oracle enc plaintextLength b mm
    let c₂ ← LeftOrRight.oracle enc plaintextLength b mm
    pure (c₁, c₂)).run s)).run tape

/-- The encryption of the counter-indexed challenger of `G₁½` at budget `qEnc`. -/
@[expose]
def counterEnc (qEnc : ℕ) : Plaintext → StateT ℕ (OracleComp (unifSpec + spec.batch)) ByteArray :=
  counterEncrypt (n := 2) (S := S) (L := L) (Salt := Salt) (Ctx := Salt) toyPRF codec qEnc pz

/-- The encryption of the counter-indexed challenger of `G₁½` at budget `qEnc`, with its log. -/
@[expose]
def counterLogEnc (qEnc : ℕ) :
    Plaintext → StateT (ℕ × CounterLog N K) (OracleComp (unifSpec + spec.batch)) ByteArray :=
  counterLogEncrypt (n := 2) (S := S) (L := L) (Salt := Salt) (Ctx := Salt) toyPRF codec qEnc pz

/-- The encryption of the private challenger of `G₁`. -/
@[expose]
def privateEnc :
    Plaintext → StateT (privateSpec N K).QueryCache (OracleComp (unifSpec + spec.batch))
      ByteArray :=
  privateEncrypt (n := 2) (S := S) (L := L) (Salt := Salt) (Ctx := Salt) toyPRF codec pz

/-- The coin tape of the countermodel: nonce `1`, subkeys `(2, 3)`, nonce `1`, subkeys `(4, 5)`. -/
@[expose]
def tape : List ℕ := [1, 2, 3, 1, 4, 5]

/-- **`G₁½`, two accepted encryptions under one nonce.** At budget `2`, both draw the nonce `1`,
and the first is under the subkeys `(2, 3)` and the second under the subkeys `(4, 5)` of its own
draw. The counter ends at `2` and the whole tape is used. -/
theorem counter_sameNonce (g : QueryImpl spec Id) :
    twoChallenges g (counterEnc 2) true (msgA, msgB) 0 tape =
      (((some (sealWith toyPRF codec pz 1 (2, 3) msgB),
        some (sealWith toyPRF codec pz 1 (4, 5) msgB)), 2), []) :=
  rfl

/-- The log of `G₁½` holds both encryptions with the nonce `1` and their distinct subkeys, the
latest first. -/
theorem counterLog_sameNonce (g : QueryImpl spec Id) :
    (twoChallenges g (counterLogEnc 2) true (msgA, msgB) (0, []) tape).1.2 =
      (2, [(1, (4, 5)), (1, (2, 3))]) :=
  rfl

/-- **`G₁`, the same two encryptions.** Both draw the nonce `1` and are under the subkeys `(2, 3)`:
the second reads them from the private cache and draws no subkey, so `[4, 5]` is left on the
tape. -/
theorem private_sameNonce (g : QueryImpl spec Id) :
    let r := twoChallenges g privateEnc true (msgA, msgB) ∅ tape
    r.1.1 = (some (sealWith toyPRF codec pz 1 (2, 3) msgB),
      some (sealWith toyPRF codec pz 1 (2, 3) msgB)) ∧ r.2 = [4, 5] := by
  refine ⟨?_, ?_⟩ <;> rfl

/-- A pair of messages of unequal length is answered with `none` by `G₁½`, leaves the counter
unchanged and draws no coin, at every budget, hidden bit, counter and tape. -/
theorem counter_unequal (g : QueryImpl spec Id) (qEnc : ℕ) (b : Bool) (j : ℕ) (tape : List ℕ) :
    twoChallenges g (counterEnc qEnc) b (msgA, msgC) j tape = (((none, none), j), tape) :=
  rfl

/-- The same through the log: the counter and the log are unchanged. -/
theorem counterLog_unequal (g : QueryImpl spec Id) (qEnc : ℕ) (b : Bool) (s : ℕ × CounterLog N K)
    (tape : List ℕ) :
    twoChallenges g (counterLogEnc qEnc) b (msgA, msgC) s tape = (((none, none), s), tape) :=
  rfl

/-- At budget `1`, an accepted pair after the first advances the counter, is answered by the empty
byte string and draws no coin. -/
theorem counter_overBudget (g : QueryImpl spec Id) (b : Bool) (tape : List ℕ) :
    twoChallenges g (counterEnc 1) b (msgA, msgB) 1 tape =
      (((some ByteArray.empty, some ByteArray.empty), 3), tape) := by
  cases b <;> rfl

/-- In the joint handler of the online phase of `G₁½`, a challenge query on a pair of messages of
unequal length is answered with `none` and leaves the cache, the counter and the log unchanged. -/
theorem counterJointImpl_unequal (encodePuzzle : Puzzle 2 S L Salt → ByteArray) (qEnc : ℕ)
    (puzzle : Puzzle 2 S L Salt) (b : Bool) (s : spec.QueryCache × (ℕ × CounterLog N K)) :
    (counterJointImpl toyPRF codec encodePuzzle qEnc puzzle b (.inl (.inr (msgA, msgC)))).run s =
      pure (none, s) := by
  rw [counterJointImpl_run_challenge]
  rfl

/-! ## The hops at a concrete adversary -/

/-- The context of a salt. -/
def mkCtx (salt : Salt) : Salt := salt + 1

/-- The initial accumulator of a context. -/
def initAcc (ctx : Salt) : S := ⟨ctx.val + 6, by omega⟩

/-- No preprocessing; the online phase asks one challenge on `msgA` and `msgB` and guesses whether
the first byte of the envelope is even. That byte is the first header byte `0x4c`, so the guess is
constant: the checks against `hidingAdv` exercise the statements, not the routing of nonces and
subkeys. -/
def hidingAdv : TimeLockPuzzle.HidingAdversary spec (Puzzle 2 S L Salt) Plaintext ByteArray where
  State := Unit
  preprocess := pure ()
  online _ _ := do
    let c ← liftM (((unifSpec + LeftOrRight.spec Plaintext ByteArray) + spec.batch).query
      (.inl (.inr (msgA, msgB))))
    return ((c.getD ByteArray.empty).data.toList.headD 0).toNat % 2 == 0

/-- `hidingAdv` makes one challenge query. -/
theorem hidingAdv_makesAtMostQueries : hidingAdv.MakesAtMostQueries 1 := by
  intro σ puzzle
  simp [hidingAdv]

variable (encodePuzzle : Puzzle 2 S L Salt → ByteArray)

/-- At budget `1` no nonce can repeat, so `G₁` and `G₁½` agree for `hidingAdv`. -/
theorem hidingAdv_private_counter (b : Bool) :
    ENNReal.absDiff
      (Pr{let z ← (simulateQ spec.romImpl
        (privateExperiment 1 toyPRF codec encodePuzzle mkCtx initAcc hidingAdv b)).run' ∅}[
          z.1 = true])
      (Pr{let z ← (simulateQ spec.romImpl
        (counterExperiment 1 toyPRF codec encodePuzzle 1 mkCtx initAcc hidingAdv b)).run' ∅}[
          z.1 = true]) ≤ 0 := by
  simpa using absDiff_privateExperiment_counterExperiment_le toyPRF codec encodePuzzle 1 mkCtx
    initAcc hidingAdv hidingAdv_makesAtMostQueries b

/-- `G₁½` is `G₂` in law for `hidingAdv` at budget `1`. -/
theorem hidingAdv_counter_eq_prfReal (b : Bool) :
    Prod.fst <$> (simulateQ spec.romImpl
        (counterExperiment 1 toyPRF codec encodePuzzle 1 mkCtx initAcc hidingAdv b)).run' ∅ =ᵈ
      (toyPRF.multiKey (Fin (2 * 1))).prfRealExperiment
        (indexedRun 1 codec encodePuzzle 1 mkCtx initAcc hidingAdv b) :=
  counterExperiment_eq_prfReal toyPRF codec encodePuzzle 1 toyPRF_uniformKey mkCtx initAcc
    hidingAdv b

/-- **The main theorem at small parameters.** For `hidingAdv` at budget `1`, `|G₁ - G₂| ≤ 1 / 8`. -/
theorem hidingAdv_private_indexed_le (b : Bool) :
    ENNReal.absDiff
      (Pr{let z ← (simulateQ spec.romImpl
        (privateExperiment 1 toyPRF codec encodePuzzle mkCtx initAcc hidingAdv b)).run' ∅}[
          z.1 = true])
      (Pr{let g ← ((toyPRF.multiKey (Fin (2 * 1))).prfRealExperiment
        (indexedRun 1 codec encodePuzzle 1 mkCtx initAcc hidingAdv b))}[g = true]) ≤ 1 / 8 := by
  have h := absDiff_privateExperiment_indexed_le (m := 1) toyPRF codec encodePuzzle 1 mkCtx initAcc
    hidingAdv toyPRF_uniformKey hidingAdv_makesAtMostQueries b
  refine h.trans (le_of_eq ?_)
  rw [Fintype.card_fin]
  norm_num

/-! ## Two identical challenges separate `G₁` from `G₁½` -/

/-- The toy keystream byte of a one-byte message determines the encryption subkey. -/
theorem xorBytes_keystream_msgA_inj : ∀ k k' : K,
    xorBytes msgA.1.data.toList (keystream toyPRF k msgA.1.size) =
      xorBytes msgA.1.data.toList (keystream toyPRF k' msgA.1.size) → k = k' := by
  decide

/-- Distinct subkeys below `7` are distinct bytes. -/
theorem uInt8_ofNat_inj : ∀ k k' : K, UInt8.ofNat k.val = UInt8.ofNat k'.val → k = k' := by
  decide

/-- The toy envelope of `msgA` determines its nonce and its two subkeys, under all puzzle bytes:
parsing reads back the nonce, the ciphertext determines the encryption subkey and the first tag
byte the MAC subkey. -/
theorem sealWith_msgA_inj (pz : ByteArray) {η η' : N} {ks ks' : K × K}
    (h : sealWith toyPRF codec pz η ks msgA = sealWith toyPRF codec pz η' ks' msgA) :
    η = η' ∧ ks = ks' := by
  have hp := congrArg (parse codec pz) h
  rw [parse_sealWith, parse_sealWith] at hp
  simp only [Option.some.injEq, Fields.mk.injEq] at hp
  obtain ⟨hη, hct, hsg, htag⟩ := hp
  rw [hsg] at htag
  have h0 := congrArg (fun x : Bytes 32 => x.toVector[0]) htag
  simp only [toyPRF, Vector.getElem_ofFn] at h0
  refine ⟨hη, Prod.ext (xorBytes_keystream_msgA_inj _ _ hct) (uInt8_ofNat_inj _ _ ?_)⟩
  simpa using h0

/-- No preprocessing; the online phase asks two challenges on `(msgA, msgA)` and guesses whether
the two answers are equal. -/
@[expose]
def pairAdv : TimeLockPuzzle.HidingAdversary spec (Puzzle 2 S L Salt) Plaintext ByteArray where
  State := Unit
  preprocess := pure ()
  online _ _ := do
    let c₁ : Option ByteArray ← liftM (((unifSpec + LeftOrRight.spec Plaintext ByteArray) +
      spec.batch).query (.inl (.inr (msgA, msgA))))
    let c₂ : Option ByteArray ← liftM (((unifSpec + LeftOrRight.spec Plaintext ByteArray) +
      spec.batch).query (.inl (.inr (msgA, msgA))))
    return decide (c₁ = c₂)

/-- `pairAdv` makes two challenge queries. -/
theorem pairAdv_makesAtMostQueries : pairAdv.MakesAtMostQueries 2 := by
  intro σ puzzle
  simp [pairAdv]

/-- The online phase of `pairAdv` under a stateful handler: two challenge steps, then the
comparison of their answers. -/
theorem run_pairAdv {σ : Type}
    (impl : QueryImpl ((unifSpec + LeftOrRight.spec Plaintext ByteArray) + spec.batch)
      (StateT σ ProbComp)) (puzzle : Puzzle 2 S L Salt) (s₀ : σ) :
    (simulateQ impl (pairAdv.online () puzzle)).run s₀ = (do
      let p : Option ByteArray × σ ← (impl (.inl (.inr (msgA, msgA)))).run s₀
      let p' : Option ByteArray × σ ← (impl (.inl (.inr (msgA, msgA)))).run p.2
      pure (decide (p.1 = p'.1), p'.2)) := by
  simp [pairAdv]

/-- A uniform draw followed by an independent uniform draw is a uniform pair. -/
theorem prEvent_uniformSample_bind_uniformSample {α β γ : Type} [SampleableType α]
    [SampleableType β] (F : α → β → γ) (p : γ → Prop) :
    Pr{let z ← ($ᵗ α >>= fun a => $ᵗ β >>= fun b => pure (F a b))}[p z] =
      Pr{let x ← $ᵗ (α × β)}[p (F x.1 x.2)] := by
  rw [SampleableType.uniformSample_prod_eq_bind, ← prEvent_map]
  simp [map_bind]

/-- In the online phase of `G₁`, the two envelopes of `pairAdv` are equal exactly when the nonces
collide, with probability `1 / 4`: the second encryption under the first nonce reads the subkeys
from the private cache, and under another nonce the envelope carries another nonce. -/
theorem prEvent_privateOnlineImpl_pairAdv (b : Bool) (puzzle : Puzzle 2 S L Salt)
    (s : spec.QueryCache) :
    Pr{let z ← (simulateQ (privateOnlineImpl (Ctx := Salt) toyPRF codec encodePuzzle puzzle b)
      (pairAdv.online () puzzle)).run (s, ∅)}[z.1 = true] = (4 : ℝ≥0∞)⁻¹ := by
  rw [run_pairAdv, privateOnlineImpl_run_challenge]
  simp only [privateOnlineImpl_run_challenge, ↓reduceIte, ite_self, bind_assoc, pure_bind,
    randomOracle.run_eq, QueryCache.empty_apply]
  refine prEvent_bind_eq_of_forall_eq _ (prEvent_true_eq_one _) _ _ fun η₁ => ?_
  refine prEvent_bind_eq_of_forall_eq _ (prEvent_true_eq_one _) _ _ fun ks₁ => ?_
  classical
  rw [prEvent_bind_eq_sum_fintype,
    show (4 : ℝ≥0∞)⁻¹ = ∑ a : N, (4 : ℝ≥0∞)⁻¹ * (if a = η₁ then 1 else 0) by simp]
  refine Finset.sum_congr rfl fun η₂ _ => ?_
  rw [SampleableType.prEvent_uniformSample_eq_singleton, Fintype.card_fin, Nat.cast_ofNat]
  congr 1
  by_cases h : η₂ = η₁
  · subst h
    simp
  · simp only [QueryCache.cacheQuery_of_ne (h := h), QueryCache.empty_apply, h, ↓reduceIte,
      bind_assoc, pure_bind]
    refine prEvent_bind_eq_of_forall_eq _ (prEvent_true_eq_one _) _ _ fun ks₂ => ?_
    rw [prEvent_pure]
    simp only [decide_eq_true_eq, Option.some.injEq, ite_eq_right_iff, one_ne_zero, imp_false]
    exact fun he => h (sealWith_msgA_inj _ he).1.symm

/-- In the online phase of `G₁½` at budget `2`, the two envelopes of `pairAdv` are equal exactly
when the nonces and both subkeys collide, with probability `1 / 196`. -/
theorem prEvent_counterJointImpl_pairAdv (b : Bool) (puzzle : Puzzle 2 S L Salt)
    (s : spec.QueryCache) :
    Pr{let z ← (simulateQ (counterJointImpl toyPRF codec encodePuzzle 2 puzzle b)
      (pairAdv.online () puzzle)).run (s, (0, []))}[z.1 = true] = (196 : ℝ≥0∞)⁻¹ := by
  rw [run_pairAdv, counterJointImpl_run_challenge]
  simp only [counterJointImpl_run_challenge, ↓reduceIte, ite_self, bind_assoc, pure_bind,
    show (0 : ℕ) < 2 from by decide, show (0 + 1 : ℕ) < 2 from by decide]
  refine prEvent_bind_eq_of_forall_eq _ (prEvent_true_eq_one _) _ _ fun η₁ => ?_
  refine prEvent_bind_eq_of_forall_eq _ (prEvent_true_eq_one _) _ _ fun ks₁ => ?_
  have hc : (196 : ℝ≥0∞)⁻¹ = (Fintype.card (N × (K × K)) : ℝ≥0∞)⁻¹ := by simp
  rw [hc, ← SampleableType.prEvent_uniformSample_eq_singleton (η₁, ks₁),
    prEvent_uniformSample_bind_uniformSample]
  refine prEvent_congr _ _ _ fun x => ?_
  simp only [decide_eq_true_eq, Option.some.injEq]
  constructor
  · intro h
    obtain ⟨h₁, h₂⟩ := sealWith_msgA_inj _ h
    exact Prod.ext h₁.symm h₂.symm
  · rintro rfl
    rfl

/-- **`G₁` for `pairAdv`.** The two envelopes are equal with probability `1 / 4`. -/
theorem privateExperiment_pairAdv (b : Bool) :
    Pr{let z ← (simulateQ spec.romImpl
      (privateExperiment 1 toyPRF codec encodePuzzle mkCtx initAcc pairAdv b)).run' ∅}[
        z.1 = true] = (4 : ℝ≥0∞)⁻¹ := by
  rw [StateT.run'_eq, prEvent_map]
  simp only [privateExperiment, TimeLockPuzzle.guessExperiment, simulateQ_bind,
    StateT.run_bind, bind_pure_comp, privateAdversary]
  refine prEvent_bind_eq_of_forall_eq _ (prEvent_true_eq_one _) _ _ fun p => ?_
  refine prEvent_bind_eq_of_forall_eq _ (prEvent_true_eq_one _) _ _ fun p₁ => ?_
  rw [simulateQ_map, StateT.run_map, prEvent_map,
    (run_romImpl_privateImpl_evalDistEq toyPRF codec encodePuzzle p₁.1.1 b _
      p₁.2).prEvent_eq, prEvent_map]
  exact prEvent_privateOnlineImpl_pairAdv encodePuzzle b p₁.1.1 p₁.2

/-- **`G₁½` for `pairAdv` at budget `2`.** The two envelopes are equal with probability
`1 / 196`. -/
theorem counterExperiment_pairAdv (b : Bool) :
    Pr{let z ← (simulateQ spec.romImpl
      (counterExperiment 1 toyPRF codec encodePuzzle 2 mkCtx initAcc pairAdv b)).run' ∅}[
        z.1 = true] = (196 : ℝ≥0∞)⁻¹ := by
  rw [StateT.run'_eq, prEvent_map]
  simp only [counterExperiment, TimeLockPuzzle.guessExperiment, simulateQ_bind,
    StateT.run_bind, bind_pure_comp, counterAdversary]
  refine prEvent_bind_eq_of_forall_eq _ (prEvent_true_eq_one _) _ _ fun p => ?_
  refine prEvent_bind_eq_of_forall_eq _ (prEvent_true_eq_one _) _ _ fun p₁ => ?_
  rw [simulateQ_map, StateT.run_map, prEvent_map,
    (run_romImpl_counterImpl_evalDistEq_counterJointImpl toyPRF codec encodePuzzle 2 p₁.1.1 b _
      p₁.2).prEvent_eq, prEvent_map]
  exact prEvent_counterJointImpl_pairAdv encodePuzzle b p₁.1.1 p₁.2

/-- `pairAdv` separates `G₁` from `G₁½`, and the nonce hop bounds the gap by `1 / 4`. -/
theorem pairAdv_separates (b : Bool) :
    Pr{let z ← (simulateQ spec.romImpl
      (privateExperiment 1 toyPRF codec encodePuzzle mkCtx initAcc pairAdv b)).run' ∅}[
        z.1 = true] ≠
      Pr{let z ← (simulateQ spec.romImpl
        (counterExperiment 1 toyPRF codec encodePuzzle 2 mkCtx initAcc pairAdv b)).run' ∅}[
          z.1 = true] ∧
    ENNReal.absDiff (4 : ℝ≥0∞)⁻¹ (196 : ℝ≥0∞)⁻¹ ≤ (4 : ℝ≥0∞)⁻¹ := by
  rw [privateExperiment_pairAdv, counterExperiment_pairAdv]
  refine ⟨by norm_num, ?_⟩
  have h := absDiff_privateExperiment_counterExperiment_le (m := 1) toyPRF codec encodePuzzle 2
    mkCtx initAcc pairAdv pairAdv_makesAtMostQueries b
  rw [privateExperiment_pairAdv, counterExperiment_pairAdv] at h
  refine h.trans (le_of_eq ?_)
  rw [Fintype.card_fin]
  norm_num
  rw [ENNReal.div_eq_inv_mul, show (8 : ℝ≥0∞) = 4 * 2 by norm_num,
    ENNReal.mul_inv (by simp) (by simp), mul_assoc, ENNReal.inv_mul_cancel (by simp) (by simp),
    mul_one]

end VCVioTest.PointerChainPuzzle.HidingNonce
