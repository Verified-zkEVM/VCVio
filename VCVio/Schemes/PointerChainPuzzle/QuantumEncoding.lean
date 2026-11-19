/-
Copyright (c) 2026 Quang Dao, Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Alexander Hicks
-/

module
public import VCVio.Schemes.PointerChainPuzzle.LeanSealBridge
public import ToMathlib.Data.ByteArray.Bounded
public import VCVio.Quantum.Oracle.Encoding
public import VCVio.CryptoFoundations.TimeLockPuzzle.QuantumClassical

/-!
# Finite byte windows for the exact pointer-chain encoding

The query input register contains every byte string up to its stated length bound, including
malformed and off-image strings. All six honest hash-input families fit in this register when
the bound is at least `max (54 + b) 83`, and in 86 bytes for every accepted link width.
The response register retains the full 32-byte hash answer, including mask tails. Public puzzles
use the structured `Puzzle` type; honest algorithms agree with `gen` and `solve` at every fixed
oracle. Resource-bounded recovery is analyzed in `QuantumCoupling.Preprocessing`;
decoding arbitrary serialized puzzles remains a separate interface obligation.
All adversary oracle inputs in this interface satisfy the explicit byte-length bound.
-/

public section

open OracleSpec OracleComp Quantum MeasureTheory
open scoped ENNReal

namespace PointerChainPuzzle.LeanSeal

/-- The largest hash-input length among the exact encoding's six oracle families. -/
@[expose]
def hashInputBound (b : ℕ) : ℕ := max (54 + b) 83

/-- Exact byte lengths of the six hash-input families. -/
theorem size_hashInput {b n : ℕ} (t : TypedPoint b n) :
    (hashInput t).size = match t with
      | .start .. => 54 + b
      | .step .. => 52
      | .mask .. => 81
      | .acc .. => 80
      | .key .. => 80
      | .commit .. => 83 := by
  rw [show (hashInput t).size = (hashInput t).data.toList.length by simp]
  cases t <;>
    simp only [hashInput, ByteArray.data_append, Array.toList_append,
      data_toList_labelled, data_toList_toByteArray, data_toList_be,
      List.length_cons, List.length_append, Bytes.length_toList,
      VCVio.Algorithms.Encoding.natToBytesBE_length, length_labelBytes,
      show "leanseal/v1/start".utf8ByteSize = 17 by decide,
      show "leanseal/v1/mask".utf8ByteSize = 16 by decide,
      show "leanseal/v1/acc".utf8ByteSize = 15 by decide,
      show "leanseal/v1/key".utf8ByteSize = 15 by decide,
      show "leanseal/v1/commit".utf8ByteSize = 18 by decide]
  omega

/-- Every honest hash input fits the exact input-length bound. -/
theorem size_hashInput_le {b n : ℕ} (t : TypedPoint b n) :
    (hashInput t).size ≤ hashInputBound b := by
  rw [size_hashInput]
  cases t <;> simp only [hashInputBound] <;> omega

/-- Every accepted link width fits all honest hash calls into a window of 86 bytes. -/
theorem hashInputBound_le_86 {b : ℕ} (hb : b ≤ 32) : hashInputBound b ≤ 86 := by
  unfold hashInputBound
  omega

/-- The exact hash-input byte string as a basis value of a sufficiently large finite register. -/
@[expose]
def hashInputWindow {b n B : ℕ} (hB : hashInputBound b ≤ B) (t : TypedPoint b n) :
    ByteArray.Bounded B :=
  ⟨hashInput t, (size_hashInput_le t).trans hB⟩

@[simp]
theorem toByteArray_hashInputWindow {b n B : ℕ} (hB : hashInputBound b ≤ B)
    (t : TypedPoint b n) : (hashInputWindow hB t).toByteArray = hashInput t := rfl

/-- Domain separation remains injective in the full finite byte window. -/
theorem hashInputWindow_injective {b n B : ℕ} (hB : hashInputBound b ≤ B) (hn : n < 2 ^ 32) :
    Function.Injective (hashInputWindow (n := n) hB) := by
  intro t u h
  exact hashInput_injective hn (congrArg ByteArray.Bounded.toByteArray h)

/-- The raw parser rejects exactly the window inputs outside the six encoded families. -/
theorem route_eq_none_iff_not_mem_range_hashInputWindow {b n B : ℕ}
    (hB : hashInputBound b ≤ B) (hn : n < 2 ^ 32) (x : ByteArray.Bounded B) :
    route (b := b) (n := n) x.toByteArray = none ↔
      x ∉ Set.range (hashInputWindow (n := n) hB) := by
  rw [route_eq_none_iff hn]
  constructor
  · rintro h ⟨t, ht⟩
    exact h t (congrArg ByteArray.Bounded.toByteArray ht)
  · intro h t ht
    exact h ⟨t, ByteArray.Bounded.toByteArray_injective ht⟩

/-! ## Completing the full raw table -/

/-- Independent typed answers, complementary answer tails and every outside-image raw cell.
All coordinates are fixed for the complete quantum run. -/
abbrev WindowTables (b n B : ℕ) (hB : hashInputBound b ≤ B) :=
  (((t : TypedPoint b n) → (typedSpec b n).Range t) ×
    ((t : TypedPoint b n) → Tail b t)) ×
      ({x : ByteArray.Bounded B // x ∉ Set.range (hashInputWindow (n := n) hB)} → Bytes 32)

instance {b n B : ℕ} {hB : hashInputBound b ≤ B} : Finite (WindowTables b n B hB) := by
  infer_instance

noncomputable instance {b n B : ℕ} {hB : hashInputBound b ≤ B} :
    Fintype (WindowTables b n B hB) := Fintype.ofFinite _

/-- The complete raw table is equivalent to its independent visible, tail and outside-image
coordinates. In particular, truncating masks does not remove their remaining output bytes. -/
@[expose]
noncomputable def windowTableEquiv {b n B : ℕ} (hb : b ≤ 32) (hn : n < 2 ^ 32)
    (hB : hashInputBound b ≤ B) :
    (ByteArray.Bounded B → Bytes 32) ≃ WindowTables b n B hB :=
  Equiv.tableSplit (hashInputWindow hB) (hashInputWindow_injective hB hn) (split hb)

/-- The typed component of a full raw response is exactly the source encoding's truncation. -/
theorem windowTableEquiv_apply_answer {b n B : ℕ} (hb : b ≤ 32) (hn : n < 2 ^ 32)
    (hB : hashInputBound b ≤ B) (H : ByteArray.Bounded B → Bytes 32)
    (t : TypedPoint b n) :
    (windowTableEquiv hb hn hB H).1.1 t = truncate t (H (hashInputWindow hB t)) := by
  rw [windowTableEquiv, Equiv.tableSplit_apply_typed]
  cases t <;> rfl

/-- The complementary component records the complete mask tail, fixed across every call. -/
theorem windowTableEquiv_apply_tail {b n B : ℕ} (hb : b ≤ 32) (hn : n < 2 ^ 32)
    (hB : hashInputBound b ≤ B) (H : ByteArray.Bounded B → Bytes 32)
    (t : TypedPoint b n) :
    (windowTableEquiv hb hn hB H).1.2 t = (split hb t (H (hashInputWindow hB t))).2 := rfl

/-- Every unencoded byte string retains its raw full-width response. -/
theorem windowTableEquiv_apply_outside {b n B : ℕ} (hb : b ≤ 32) (hn : n < 2 ^ 32)
    (hB : hashInputBound b ≤ B) (H : ByteArray.Bounded B → Bytes 32)
    (x : {x : ByteArray.Bounded B // x ∉ Set.range (hashInputWindow (n := n) hB)}) :
    (windowTableEquiv hb hn hB H).2 x = H x := rfl

/-- Reassembling the table at an encoded point rejoins its typed answer and complete tail. -/
theorem windowTableEquiv_symm_apply_input {b n B : ℕ} (hb : b ≤ 32) (hn : n < 2 ^ 32)
    (hB : hashInputBound b ≤ B) (tables : WindowTables b n B hB) (t : TypedPoint b n) :
    (windowTableEquiv hb hn hB).symm tables (hashInputWindow hB t) =
      (split hb t).symm (tables.1.1 t, tables.1.2 t) :=
  Equiv.tableSplit_symm_apply_encode _ _ _ _ _

/-- Every raw quantum program has the same joint observed law after full-table completion.
The program and query signature are unchanged, so cross-domain superpositions, arbitrary
outside-image queries, all response bits and retained quantum memory are preserved. -/
theorem sampledEvalDistMap_windowTableEquiv {b n B : ℕ}
    (hb : b ≤ 32) (hn : n < 2 ^ 32) (hB : hashInputBound b ≤ B)
    {L : LocalSig} {W : QReg → Type*} {A : QReg} (I : L.Interp)
    (x : QuantumComp L (qromBatchSpec (ByteArray.Bounded B) (Bytes 32)) W A) (ρ : SubState A)
    {Out : Type*} [MeasurableSpace Out]
    (f : (ByteArray.Bounded B → Bytes 32) → (Σ C, W C) → Out) :
    sampledEvalDistMap parallelOracleRuntime I x ρ f =
      sampledEvalDistMap
        (fun tables ↦ parallelOracleRuntime ((windowTableEquiv hb hn hB).symm tables))
        I x ρ (fun tables ↦ f ((windowTableEquiv hb hn hB).symm tables)) :=
  Quantum.sampledEvalDistMap_tableSplit (hashInputWindow hB)
    (hashInputWindow_injective hB hn) (split hb) I x ρ f

/-! ## The honest scheme over the complete finite byte window -/

/-- The raw hash oracle on every byte string of length at most `B`. -/
abbrev windowSpec (B : ℕ) : OracleSpec (ByteArray.Bounded B) :=
  ByteArray.Bounded B →ₒ Bytes 32

/-- Extend a window table by zero outside the window. Honest calls are all in the window,
so their behavior is independent of this choice of outside values. -/
@[expose]
def extendWindowOracle {B : ℕ} (H : ByteArray.Bounded B → Bytes 32) (x : ByteArray) : Bytes 32 :=
  if hx : x.size ≤ B then H ⟨x, hx⟩ else 0

@[simp]
theorem extendWindowOracle_apply {B : ℕ} (H : ByteArray.Bounded B → Bytes 32)
    (x : ByteArray.Bounded B) : extendWindowOracle H x.toByteArray = H x := by
  change (if hx : x.val.size ≤ B then H ⟨x.val, hx⟩ else 0) = H x
  rw [dite_eq_left x.property]

/-- Typed round answers obtained by truncating full raw window responses. -/
@[expose]
def truncateWindowRound {b n B : ℕ} (hB : hashInputBound b ≤ B) (ts : List (TypedPoint b n))
    (us : (windowSpec B).batch.Range (ts.map (hashInputWindow hB))) :
    (typedSpec b n).batch.Range ts :=
  fun j ↦ truncate ts[j] (us ⟨j, by simp⟩)

/-- An exact typed hash-input round submitted within the complete finite raw window. -/
@[expose]
def windowRoundImpl {b n B : ℕ} (hB : hashInputBound b ≤ B) :
    QueryImpl (unifSpec + (typedSpec b n).batch)
      (OracleComp (unifSpec + (windowSpec B).batch))
  | .inl k => liftM ((unifSpec + (windowSpec B).batch).query (.inl k))
  | .inr ts =>
      truncateWindowRound hB ts <$>
        liftM ((unifSpec + (windowSpec B).batch).query
          (.inr (ts.map (hashInputWindow hB))))

/-- The exact pointer-chain generator and checked solver over the full finite byte window.
Only their own queries are encoded typed points; an adversary's raw access remains unrestricted
within the window. -/
@[expose]
def windowScheme {b n B : ℕ} (hB : hashInputBound b ≤ B) (m : ℕ) [NeZero n] :
    _root_.TimeLockPuzzle (windowSpec B) (Puzzle b n) (Bytes 32) where
  gen := simulateQ (windowRoundImpl hB) (PointerChainPuzzle.gen m (ctx b n m) id)
  solve puzzle := simulateQ (windowRoundImpl hB) (PointerChainPuzzle.solve m (ctx b n m) id puzzle)

/-- The raw finite oracle answered by one fixed complete table, with local coins forwarded. -/
abbrev windowImpl {B : ℕ} (H : ByteArray.Bounded B → Bytes 32) :
    QueryImpl (unifSpec + (windowSpec B).batch) ProbComp :=
  (unifFwdAnswerImpl (QueryImpl.ofFn H)).batch'

/-- Encoded honest rounds agree with any byte-answer function having the same encoded cells.
No hypothesis restricts that byte-answer function outside these cells. -/
theorem windowImpl_compose_windowRoundImpl_of_agree {b n B : ℕ}
    (hB : hashInputBound b ≤ B) (H : ByteArray.Bounded B → Bytes 32)
    (h : ByteArray → Bytes 32)
    (hH : ∀ t : TypedPoint b n, H (hashInputWindow hB t) = h (hashInput t)) :
    windowImpl H ∘ₛ windowRoundImpl (n := n) hB = impl h b n := by
  funext t
  rcases t with k | ts
  · rw [QueryImpl.apply_compose, windowRoundImpl, simulateQ_spec_query]
    rfl
  · rw [QueryImpl.apply_compose, windowRoundImpl, simulateQ_map, simulateQ_spec_query]
    simp only [windowImpl, impl, QueryImpl.batch'_apply_inr]
    rw [QueryImpl.batch_unifFwdAnswerImpl, QueryImpl.batch_unifFwdAnswerImpl]
    refine (map_pure _ _).trans (congrArg pure (funext fun j ↦ ?_))
    rw [toImpl_oracles_apply]
    simpa [truncateWindowRound, Id.run] using congrArg (truncate ts[j]) (hH ts[j])

/-- Answering encoded honest rounds with a finite raw table agrees with the source byte
encoding at its extension. This identity needs no injectivity or truncation-width assumptions. -/
theorem windowImpl_compose_windowRoundImpl {b n B : ℕ} (hB : hashInputBound b ≤ B)
    (H : ByteArray.Bounded B → Bytes 32) :
    windowImpl H ∘ₛ windowRoundImpl (n := n) hB = impl (extendWindowOracle H) b n := by
  apply windowImpl_compose_windowRoundImpl_of_agree
  intro t
  exact (extendWindowOracle_apply H (hashInputWindow hB t)).symm

/-- The finite-window generator computes the exact source byte-level generator. -/
theorem simulateQ_windowScheme_gen {b n B : ℕ} (hB : hashInputBound b ≤ B)
    (H : ByteArray.Bounded B → Bytes 32) (m : ℕ) [NeZero n] :
    simulateQ (windowImpl H) (windowScheme (n := n) hB m).gen = gen (extendWindowOracle H) m := by
  rw [windowScheme, ← QueryImpl.simulateQ_compose,
    windowImpl_compose_windowRoundImpl, simulateQ_gen_eq]

/-- The finite-window checked solver computes the exact source byte-level solver on every
puzzle, including puzzles not produced by generation. -/
theorem simulateQ_windowScheme_solve {b n B : ℕ} (hB : hashInputBound b ≤ B)
    (H : ByteArray.Bounded B → Bytes 32) (m : ℕ) [NeZero n] (puzzle : Puzzle b n) :
    simulateQ (windowImpl H) ((windowScheme hB m).solve puzzle) =
      pure (solve (extendWindowOracle H) m puzzle) := by
  rw [windowScheme, ← QueryImpl.simulateQ_compose,
    windowImpl_compose_windowRoundImpl, simulateQ_solve_eq]

/-- Restricting any byte-answer function to the window preserves honest generation. -/
theorem simulateQ_windowScheme_gen_restrict {b n B : ℕ} (hB : hashInputBound b ≤ B)
    (h : ByteArray → Bytes 32) (m : ℕ) [NeZero n] :
    simulateQ (windowImpl (fun x : ByteArray.Bounded B ↦ h x.toByteArray))
      (windowScheme (n := n) hB m).gen = gen h m := by
  rw [windowScheme, ← QueryImpl.simulateQ_compose,
    windowImpl_compose_windowRoundImpl_of_agree hB _ h (fun _ ↦ rfl), simulateQ_gen_eq]

/-- Restricting any byte-answer function to the window preserves the checked solver on every
puzzle. The values outside the window are arbitrary. -/
theorem simulateQ_windowScheme_solve_restrict {b n B : ℕ} (hB : hashInputBound b ≤ B)
    (h : ByteArray → Bytes 32) (m : ℕ) [NeZero n] (puzzle : Puzzle b n) :
    simulateQ (windowImpl (fun x : ByteArray.Bounded B ↦ h x.toByteArray))
      ((windowScheme hB m).solve puzzle) = pure (solve h m puzzle) := by
  rw [windowScheme, ← QueryImpl.simulateQ_compose,
    windowImpl_compose_windowRoundImpl_of_agree hB _ h (fun _ ↦ rfl), simulateQ_solve_eq]

/-- The quantum honest scheme embeds the exact finite-window generator and checked solver.
Its adversary may retain arbitrary quantum memory between preprocessing and online execution. -/
@[expose, reducible]
noncomputable def quantumWindowScheme {b n B : ℕ} (hB : hashInputBound b ≤ B)
    (m : ℕ) [NeZero n] :
    Quantum.TimeLockPuzzle (qromBatchSpec (ByteArray.Bounded B) (Bytes 32))
      (Puzzle b n) (Bytes 32) :=
  Quantum.TimeLockPuzzle.ofClassicalGenerator
    ((fun pk : Puzzle b n × Bytes 32 ↦ (pk.1, pk.2, ())) <$>
      (windowScheme (n := n) hB m).gen)
    (fun puzzle ↦ ((windowScheme hB m).solve puzzle).toQuantumBatch)

/-- The concrete finite-window scheme is the standard quantum embedding of its honest programs. -/
theorem quantumWindowScheme_eq_toQuantum {b n B : ℕ} (hB : hashInputBound b ≤ B)
    (m : ℕ) [NeZero n] :
    quantumWindowScheme (n := n) hB m = (windowScheme (n := n) hB m).toQuantum := rfl

/-- Honest quantum generation has exactly the source byte-generator law, with its auxiliary
unit secret retained. Only the finite input window restricts the oracle model. -/
theorem evalDist_quantumWindowScheme_gen {b n B : ℕ} (hB : hashInputBound b ≤ B)
    (H : ByteArray.Bounded B → Bytes 32) (m : ℕ) [NeZero n]
    [MeasurableSpace (Puzzle b n × Bytes 32 × Unit)] :
    (parallelOracleRuntime H).evalDist₂ .instruments (quantumWindowScheme (n := n) hB m).gen
        (SubState.basis ()) =
      𝒟[(fun pk : Puzzle b n × Bytes 32 ↦ (pk.1, pk.2, ())) <$>
        gen (extendWindowOracle H) m] := by
  change (parallelOracleRuntime H).evalDist₂ .instruments
    ((fun pk : Puzzle b n × Bytes 32 ↦ (pk.1, pk.2, ())) <$>
      (windowScheme (n := n) hB m).gen).toQuantumBatch (SubState.basis ()) = _
  rw [evalDist_parallelOracleRuntime_toQuantumBatch, simulateQ_map, simulateQ_windowScheme_gen]

/-- The quantum checked solver agrees with the source byte solver on every puzzle, for the
chosen output measurable space. The space need not be discrete. -/
theorem evalDist_quantumWindowScheme_solve {b n B : ℕ} (hB : hashInputBound b ≤ B)
    (H : ByteArray.Bounded B → Bytes 32) (m : ℕ) [NeZero n]
    (outputSpace : MeasurableSpace (Option (Bytes 32))) (puzzle : Puzzle b n) :
    letI := outputSpace
    (parallelOracleRuntime H).evalDist₂ .instruments ((quantumWindowScheme hB m).solve puzzle)
        (SubState.basis ()) =
      Measure.dirac (solve (extendWindowOracle H) m puzzle) := by
  let : MeasurableSpace (Option (Bytes 32)) := outputSpace
  change (parallelOracleRuntime H).evalDist₂ .instruments
    ((windowScheme hB m).solve puzzle).toQuantumBatch (SubState.basis ()) = _
  rw [evalDist_parallelOracleRuntime_toQuantumBatch, simulateQ_windowScheme_solve, evalDist_pure]

/-- Completing the sampled table preserves the exact scheme's whole three-phase experiment,
including arbitrary preprocessing, retained memory and parameter-dependent transcript checks. -/
theorem sampledDelayLawWith_quantumWindowScheme {b n B : ℕ}
    (hb : b ≤ 32) (hn : n < 2 ^ 32) (hB : hashInputBound b ≤ B) (m : ℕ) [NeZero n]
    {Out Obs : Type} [MeasurableSpace Obs]
    (adv : Quantum.TimeLockPuzzle.TwoPhaseAdversary
      (qromBatchSpec (ByteArray.Bounded B) (Bytes 32)) (Puzzle b n) Out)
    (f : (ByteArray.Bounded B → Bytes 32) →
      Quantum.TimeLockPuzzle.DelayTranscript (quantumWindowScheme hB m) adv → Obs) :
    Quantum.TimeLockPuzzle.sampledDelayLawWith parallelOracleRuntime
        (quantumWindowScheme hB m) adv f =
      Quantum.TimeLockPuzzle.sampledDelayLawWith
        (fun tables ↦ parallelOracleRuntime ((windowTableEquiv hb hn hB).symm tables))
        (quantumWindowScheme hB m) adv (fun tables ↦ f ((windowTableEquiv hb hn hB).symm tables)) :=
  Quantum.TimeLockPuzzle.sampledDelayLawWith_equiv (windowTableEquiv hb hn hB).symm
    parallelOracleRuntime (quantumWindowScheme hB m) adv f

/-- The actual scheme's key-recovery probability is unchanged by full-table completion.
This exact identity assumes no adversary query budget and proves no delay bound. -/
theorem qromDelayAdvantage_quantumWindowScheme {b n B : ℕ}
    (hb : b ≤ 32) (hn : n < 2 ^ 32) (hB : hashInputBound b ≤ B) (m : ℕ) [NeZero n]
    (adv : Quantum.TimeLockPuzzle.Adversary
      (qromBatchSpec (ByteArray.Bounded B) (Bytes 32)) (Puzzle b n) (Bytes 32)) :
    Quantum.TimeLockPuzzle.qromDelayAdvantage (quantumWindowScheme hB m) adv =
      Quantum.TimeLockPuzzle.sampledDelayAdvantage
        (fun tables ↦ parallelOracleRuntime ((windowTableEquiv hb hn hB).symm tables))
        (quantumWindowScheme hB m) adv :=
  Quantum.TimeLockPuzzle.sampledDelayAdvantage_equiv (windowTableEquiv hb hn hB).symm
    parallelOracleRuntime (quantumWindowScheme hB m) adv

end PointerChainPuzzle.LeanSeal
