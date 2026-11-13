/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Auxiliary.ChainSelection
import all HashSig.GXMSS.Security.Auxiliary.ChainSelection
public import HashSig.GXMSS.Security.Interval.Auxiliary.Interaction

/-!
# Adaptive interval chain splice views

A positive chain response determines every later prefix and the resulting public root and paths.
Both ordinary and spliced signing callbacks use the common first-request handler. Successful
records retain the complete signature and its exact encoding witness.
-/

public section
namespace GXMSS.Reductions
open OracleComp OracleSpec IncomparableEncoding SyncSignatureUnforgeability
variable {PP T X H M R : Type} {h w v : ℕ}

/-- Chain family spliced at the guessed positive position using the challenge image itself. -/
private def splicedChainValue (hash : HashInstance PP T X H h w v) (pp : PP)
    (guess : Guess h w v) (answer : H) (starts : Epoch h → Fin v → H)
    (ep : Epoch h) (i : Fin v) (position : ℕ) : H :=
  if _htarget : ep = guessedEpoch guess ∧ i = guessedChain guess then
    if position < (guessedPosition guess).val + 1 then
      hash.chain pp ep i 0 position (starts ep i)
    else hash.chain pp ep i ((guessedPosition guess).val + 1)
      (position - ((guessedPosition guess).val + 1)) answer
  else hash.chain pp ep i 0 position (starts ep i)

/-- Supplying the honest response at a cut reproduces every original chain prefix. -/
private theorem splicedChainValue_honest
    (hash : HashInstance PP T X H h w v) (pp : PP)
    (guess : Guess h w v) (starts : Epoch h → Fin v → H)
    (ep : Epoch h) (i : Fin v) (position : ℕ) :
    splicedChainValue hash pp guess
      (hash.chain pp (guessedEpoch guess) (guessedChain guess) 0
        ((guessedPosition guess).val + 1)
        (starts (guessedEpoch guess) (guessedChain guess))) starts ep i position =
      hash.chain pp ep i 0 position (starts ep i) := by
  unfold splicedChainValue
  split_ifs with htarget hbefore
  · rfl
  · rcases htarget with ⟨hepoch, hchain⟩
    subst ep
    subst i
    have hle : (guessedPosition guess).val + 1 ≤ position := by omega
    simpa [Nat.add_sub_of_le hle] using
      (hash.chain_add pp (guessedEpoch guess) (guessedChain guess) 0
        ((guessedPosition guess).val + 1)
        (position - ((guessedPosition guess).val + 1))
        (starts (guessedEpoch guess) (guessedChain guess))).symm
  · rfl

/-- Advancing a splice by one chain step leaves every later prefix unchanged when the later
answer is the hash of the earlier answer. -/
private theorem splicedChainValue_advance
    (hash : HashInstance PP T X H h w v) (pp : PP)
    (guess₁ guess₂ : Guess h w v) (answer : H)
    (starts : Epoch h → Fin v → H) (ep : Epoch h) (i : Fin v) (position : ℕ)
    (hepoch : guessedEpoch guess₁ = guessedEpoch guess₂)
    (hchain : guessedChain guess₁ = guessedChain guess₂)
    (hnext : (guessedPosition guess₂).val = (guessedPosition guess₁).val + 1)
    (hlate : (guessedPosition guess₂).val + 1 ≤ position) :
    splicedChainValue hash pp guess₁ answer starts ep i position =
      splicedChainValue hash pp guess₂
        (hash.chain pp (guessedEpoch guess₁) (guessedChain guess₁)
          ((guessedPosition guess₁).val + 1) 1 answer) starts ep i position := by
  unfold splicedChainValue
  by_cases htarget : ep = guessedEpoch guess₁ ∧ i = guessedChain guess₁
  · have htarget₂ : ep = guessedEpoch guess₂ ∧ i = guessedChain guess₂ := by
      simpa only [← hepoch, ← hchain] using htarget
    simp only [htarget]
    have hlate₁ : ¬position < (guessedPosition guess₁).val + 1 := by omega
    have hlate₂ : ¬position < (guessedPosition guess₂).val + 1 := by omega
    simp only [hlate₁, hlate₂, ↓reduceIte]
    rcases htarget with ⟨rfl, rfl⟩
    have hcount : position - ((guessedPosition guess₁).val + 1) =
        1 + (position - ((guessedPosition guess₂).val + 1)) := by omega
    rw [hcount, hash.chain_add]
    simp [hnext, hepoch, hchain]
  · have htarget₂ : ¬(ep = guessedEpoch guess₂ ∧ i = guessedChain guess₂) := by
      simpa only [← hepoch, ← hchain] using htarget
    simp [htarget, htarget₂]

private def splicedEndpoints (hash : HashInstance PP T X H h w v) (pp : PP)
    (guess : Guess h w v) (answer : H) (starts : Epoch h → Fin v → H) :
    Epoch h → Fin v → H := fun ep i =>
  splicedChainValue hash pp guess answer starts ep i (2 ^ w - 1)

private theorem splicedEndpoints_honest
    (hash : HashInstance PP T X H h w v) (pp : PP)
    (guess : Guess h w v) (starts : Epoch h → Fin v → H) :
    splicedEndpoints hash pp guess
      (hash.chain pp (guessedEpoch guess) (guessedChain guess) 0
        ((guessedPosition guess).val + 1)
        (starts (guessedEpoch guess) (guessedChain guess))) starts =
      GXMSS.endpoints hash pp starts := by
  funext ep i
  exact splicedChainValue_honest hash pp guess starts ep i _

private theorem splicedEndpoints_advance
    (hash : HashInstance PP T X H h w v) (pp : PP)
    (guess₁ guess₂ : Guess h w v) (answer : H)
    (starts : Epoch h → Fin v → H)
    (hepoch : guessedEpoch guess₁ = guessedEpoch guess₂)
    (hchain : guessedChain guess₁ = guessedChain guess₂)
    (hnext : (guessedPosition guess₂).val = (guessedPosition guess₁).val + 1) :
    splicedEndpoints hash pp guess₁ answer starts =
      splicedEndpoints hash pp guess₂
        (hash.chain pp (guessedEpoch guess₁) (guessedChain guess₁)
          ((guessedPosition guess₁).val + 1) 1 answer) starts := by
  funext ep i
  apply splicedChainValue_advance hash pp guess₁ guess₂ answer starts ep i
    (2 ^ w - 1) hepoch hchain hnext
  exact (guessedPosition guess₂).isLt

/-- Splicing the final hash response makes the selected endpoint exactly the response. -/
private theorem splicedEndpoints_guess_final
    (hash : HashInstance PP T X H h w v) (pp : PP)
    (guess : Guess h w v) (answer : H) (starts : Epoch h → Fin v → H)
    (hfinal : (guessedPosition guess).val + 1 = 2 ^ w - 1) :
    splicedEndpoints hash pp guess answer starts
      (guessedEpoch guess) (guessedChain guess) = answer := by
  rcases guess with ⟨ep, i, pos⟩
  dsimp [guessedEpoch, guessedChain, guessedPosition] at hfinal ⊢
  simp [splicedEndpoints, splicedChainValue, guessedEpoch, guessedChain,
    guessedPosition, hfinal]

/-- Deterministic tree assembly and epoch eligibility shared by chain splice interpreters.
The root and path depend on endpoints rather than the hidden start table. -/
private structure ChainSimulationContext (PP H : Type) (h v : ℕ) where
  activity : Epoch h → Bool
  root : PP → (Epoch h → Fin v → H) → H
  path : PP → (Epoch h → Fin v → H) → Epoch h → Fin h → H

private def contextSplicedSignatureOfWord (hash : HashInstance PP T X H h w v)
    (ctx : ChainSimulationContext PP H h v) (pp : PP)
    (guess : Guess h w v) (answer : H) (starts : Epoch h → Fin v → H)
    (endpoints : Epoch h → Fin v → H) (ep : Epoch h) (wr : Codeword v (2 ^ w) × R) :
    GXMSS.Signature R H h v :=
  ⟨wr.2, fun i => splicedChainValue hash pp guess answer starts ep i (wr.1 i),
    ctx.path pp endpoints ep⟩

private theorem contextSplicedSignatureOfWord_advance
    (hash : HashInstance PP T X H h w v) (ctx : ChainSimulationContext PP H h v) (pp : PP)
    (guess₁ guess₂ : Guess h w v) (answer : H)
    (starts : Epoch h → Fin v → H) (ep : Epoch h)
    (wr : Codeword v (2 ^ w) × R)
    (hepoch : guessedEpoch guess₁ = guessedEpoch guess₂)
    (hchain : guessedChain guess₁ = guessedChain guess₂)
    (hnext : (guessedPosition guess₂).val = (guessedPosition guess₁).val + 1)
    (hword : ep = guessedEpoch guess₁ →
      (guessedPosition guess₂).val + 1 ≤ (wr.1 (guessedChain guess₁)).val) :
    contextSplicedSignatureOfWord hash ctx pp guess₁ answer starts
      (splicedEndpoints hash pp guess₁ answer starts) ep wr =
    contextSplicedSignatureOfWord hash ctx pp guess₂
      (hash.chain pp (guessedEpoch guess₁) (guessedChain guess₁)
        ((guessedPosition guess₁).val + 1) 1 answer) starts
      (splicedEndpoints hash pp guess₂
        (hash.chain pp (guessedEpoch guess₁) (guessedChain guess₁)
          ((guessedPosition guess₁).val + 1) 1 answer) starts) ep wr := by
  have hend := splicedEndpoints_advance hash pp guess₁ guess₂ answer starts
    hepoch hchain hnext
  have hots : (fun i => splicedChainValue hash pp guess₁ answer starts ep i (wr.1 i)) =
      (fun i => splicedChainValue hash pp guess₂
        (hash.chain pp (guessedEpoch guess₁) (guessedChain guess₁)
          ((guessedPosition guess₁).val + 1) 1 answer) starts ep i (wr.1 i)) := by
    funext i
    by_cases htarget : ep = guessedEpoch guess₁ ∧ i = guessedChain guess₁
    · have hi : (guessedPosition guess₂).val + 1 ≤ (wr.1 i).val := by
        simpa only [htarget.2] using hword htarget.1
      exact splicedChainValue_advance hash pp guess₁ guess₂ answer starts ep i
        (wr.1 i).val hepoch hchain hnext hi
    · have htarget₂ : ¬(ep = guessedEpoch guess₂ ∧ i = guessedChain guess₂) := by
        simpa only [← hepoch, ← hchain] using htarget
      simp [splicedChainValue, htarget, htarget₂]
  simp only [contextSplicedSignatureOfWord, hots, hend]

/-- At the selected positive digit, a spliced successful signature reveals the challenge
response itself as its OTS value. -/
private theorem contextSplicedSignatureOfWord_guess_succ
    (hash : HashInstance PP T X H h w v) (ctx : ChainSimulationContext PP H h v) (pp : PP)
    (guess : Guess h w v) (answer : H) (starts endpoints : Epoch h → Fin v → H)
    (ep : Epoch h) (wr : Codeword v (2 ^ w) × R)
    (hepoch : ep = guessedEpoch guess)
    (hword : (wr.1 (guessedChain guess)).val = (guessedPosition guess).val + 1) :
    (contextSplicedSignatureOfWord hash ctx pp guess answer starts endpoints ep wr).ots
      (guessedChain guess) = answer := by
  subst ep
  rcases guess with ⟨ep, i, pos⟩
  dsimp [guessedEpoch, guessedChain, guessedPosition] at hword ⊢
  simp [contextSplicedSignatureOfWord, splicedChainValue, guessedEpoch, guessedChain,
    guessedPosition, hword]

/-- Complete internal result, including secret data unavailable to the source adversary. -/
private structure Result (PP H M R : Type) (h v : ℕ) where
  /-- Public key given to the source adversary. -/
  pk : GXMSS.PublicKey PP H
  /-- Generated secret material retained only for internal game reasoning. -/
  sk : GXMSS.SecretKey PP H h v
  /-- Epoch, message and signature returned as the candidate forgery. -/
  forgery : SyncSignatureUnforgeability.Forgery (Epoch h) M (GXMSS.Signature R H h v)
  /-- First signing-request record at each epoch, including returned failure. -/
  history : SyncSignatureUnforgeability.History (Epoch h) M (GXMSS.Signature R H h v)

private def contextSplicedSuccessfulHistoryEncodes
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w))
    (ctx : ChainSimulationContext PP H h v) (pp : PP) (guess : Guess h w v) (answer : H)
    (starts endpoints : Epoch h → Fin v → H)
    (history : SyncSignatureUnforgeability.History (Epoch h) M
      (GXMSS.Signature R H h v)) : Prop :=
  ∀ ep msg sig, history ep = some (msg, some sig) →
    ∃ wr, sig = contextSplicedSignatureOfWord hash ctx pp guess answer starts endpoints ep wr ∧
      enc.value pp msg wr.2 ep = some wr.1
/-- The actual callback skips encoding samples at inactive epochs. -/
private def contextSplicedSign [SampleableType R]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (ctx : ChainSimulationContext PP H h v) (pp : PP)
    (guess : Guess h w v) (answer : H) (starts endpoints : Epoch h → Fin v → H)
    (ep : Epoch h) (msg : M) : ProbComp (Option (GXMSS.Signature R H h v)) :=
  if ctx.activity ep then
    (fun wr => wr.map
      (contextSplicedSignatureOfWord hash ctx pp guess answer starts endpoints ep)) <$>
      enc.retry ($ᵗ R) pp msg ep K
  else pure none

private def contextSplicedSigningOracle [SampleableType R]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (ctx : ChainSimulationContext PP H h v) (pp : PP)
    (guess : Guess h w v) (answer : H) (starts endpoints : Epoch h → Fin v → H) :=
  signingKernelOracle (contextSplicedSign hash enc K ctx pp guess answer starts endpoints)

private theorem contextSplicedSign_full [SampleableType R]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (ctx : ChainSimulationContext PP H h v) (pp : PP)
    (guess : Guess h w v) (answer : H) (starts endpoints : Epoch h → Fin v → H)
    (ep : Epoch h) (msg : M) (sig : GXMSS.Signature R H h v)
    (hs : some sig ∈ support
      (contextSplicedSign hash enc K ctx pp guess answer starts endpoints ep msg)) :
    ∃ wr, sig = contextSplicedSignatureOfWord hash ctx pp guess answer starts endpoints ep wr ∧
      enc.value pp msg wr.2 ep = some wr.1 := by
  unfold contextSplicedSign at hs
  split at hs
  · simp only [support_map, Set.mem_image] at hs
    obtain ⟨answer, hanswer, heq⟩ := hs
    cases answer with
    | none => simp at heq
    | some wr =>
      refine ⟨wr, ?_, IncomparableEncoding.Retry.value_eq_some_of_mem_retry enc
        ($ᵗ R) pp msg ep K wr.1 wr.2 hanswer⟩
      simpa using heq.symm
  · simp at hs

private theorem contextSplicedSigningOracle_preserves_successfulHistoryEncodes
    [SampleableType R]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (ctx : ChainSimulationContext PP H h v) (pp : PP) (guess : Guess h w v) (answer : H)
    (starts endpoints : Epoch h → Fin v → H) (q : Epoch h × M)
    (history : History (Epoch h) M (GXMSS.Signature R H h v))
    (hinv : contextSplicedSuccessfulHistoryEncodes hash enc ctx pp guess answer starts
      endpoints history)
    (out : Option (GXMSS.Signature R H h v) × History (Epoch h) M (GXMSS.Signature R H h v))
    (hout : out ∈ support
      ((contextSplicedSigningOracle hash enc K ctx pp guess answer starts endpoints q).run
        history)) :
    contextSplicedSuccessfulHistoryEncodes hash enc ctx pp guess answer starts endpoints out.2 :=
  signingKernelOracle_preserves_successfulHistorySatisfies _ _
    (contextSplicedSign_full hash enc K ctx pp guess answer starts endpoints)
    q history hinv out hout

private def runContextSpliced [SampleableType R]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (ctx : ChainSimulationContext PP H h v)
    (adv : SchemeAdversary PP H M R h v) (pp : PP) (guess : Guess h w v)
    (answer : H) (starts : Epoch h → Fin v → H) : ProbComp (Result PP H M R h v) := do
  let endpoints := splicedEndpoints hash pp guess answer starts
  let pk : GXMSS.PublicKey PP H := ⟨ctx.root pp endpoints, pp⟩
  let sk : GXMSS.SecretKey PP H h v := ⟨pp, starts, endpoints⟩
  let (forgery, history) ← runWithSigningKernel
    (contextSplicedSign hash enc K ctx pp guess answer starts endpoints)
    (adv.forge pk) emptyHistory
  pure ⟨pk, sk, forgery, history⟩

private theorem runContextSpliced_successful_record_signature [SampleableType R]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (ctx : ChainSimulationContext PP H h v)
    (adv : SchemeAdversary PP H M R h v) (pp : PP) (guess : Guess h w v)
    (answer : H) (starts : Epoch h → Fin v → H) (out : Result PP H M R h v)
    (hout : out ∈ support (runContextSpliced hash enc K ctx adv pp guess answer starts))
    (ep : Epoch h) (msg : M) (sig : GXMSS.Signature R H h v)
    (hrecord : out.history ep = some (msg, some sig)) :
    ∃ wr, sig = contextSplicedSignatureOfWord hash ctx pp guess answer starts
        (splicedEndpoints hash pp guess answer starts) ep wr ∧
      enc.value pp msg wr.2 ep = some wr.1 := by
  unfold runContextSpliced at hout
  rw [mem_support_bind_iff] at hout
  obtain ⟨⟨forgery, history⟩, hrun, hreturn⟩ := hout
  simp only [support_pure, Set.mem_singleton_iff] at hreturn
  subst out
  exact runWithSigningKernel_preserves_successfulHistorySatisfies _ _
    (contextSplicedSign_full hash enc K ctx pp guess answer starts _)
    (adv.forge _) emptyHistory (successfulHistorySatisfies_empty _) _ hrun ep msg sig hrecord

end GXMSS.Reductions

namespace GXMSS.Interval.Reductions
open OracleComp OracleSpec GXMSS.IntervalMerkle GXMSS.Reductions SyncSignatureUnforgeability
    IncomparableEncoding
variable {PP T X H M R : Type} {h w v : ℕ}

/-- One retained filler table determines every root and path in the splice sequence. -/
private def intervalChainContext (P : HashInstance PP T X H h w v) (I : Interval h)
    (fillers : Fillers I H) : ChainSimulationContext PP H h v :=
  ⟨fun ep => decide (Epoch.IsActive I ep),
    fun pp endpoints => GXMSS.IntervalMerkle.root P I pp endpoints fillers,
    fun pp endpoints ep => GXMSS.IntervalMerkle.authPath P I pp endpoints fillers ep⟩

private def intervalSplicedSignatureOfWord (P : HashInstance PP T X H h w v) (I : Interval h)
    (pp : PP) (guess : Guess h w v) (response : H) (starts : Epoch h → Fin v → H)
    (endpoints : Epoch h → Fin v → H) (fillers : Fillers I H) (ep : Epoch h)
    (wr : Codeword v (2 ^ w) × R) : GXMSS.Signature R H h v :=
  let (word, randomizer) := wr
  ⟨randomizer, fun i => splicedChainValue P pp guess response starts ep i (word i),
    GXMSS.IntervalMerkle.authPath P I pp endpoints fillers ep⟩
private def intervalSplicedSign [SampleableType R]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (pp : PP) (guess : Guess h w v) (response : H) (starts endpoints : Epoch h → Fin v → H)
    (fillers : Fillers I H) :=
  contextSplicedSign P enc K (intervalChainContext P I fillers)
    pp guess response starts endpoints

private def intervalSplicedSigningOracle [SampleableType R]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (pp : PP) (guess : Guess h w v) (response : H) (starts endpoints : Epoch h → Fin v → H)
    (fillers : Fillers I H) :=
  signingKernelOracle (intervalSplicedSign P enc K I pp guess response starts endpoints fillers)

private theorem intervalSplicedSigningOracle_eq_context [SampleableType R]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (pp : PP) (guess : Guess h w v) (response : H) (starts endpoints : Epoch h → Fin v → H)
    (fillers : Fillers I H) :
    intervalSplicedSigningOracle P enc K I pp guess response starts endpoints fillers =
      contextSplicedSigningOracle P enc K (intervalChainContext P I fillers)
        pp guess response starts endpoints := rfl

/-- The entire adaptive view retains the public key, candidate forgery and all first records. -/
noncomputable def chainSpliceView [SampleableType R]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : SchemeAdversary PP H M R h v) (pp : PP) (guess : Guess h w v)
    (response : H) (starts : Epoch h → Fin v → H) (fillers : Fillers I H) :
    ProbComp (ExperimentResult (GXMSS.PublicKey PP H) (Epoch h) M
      (GXMSS.Signature R H h v)) := do
  let endpoints := splicedEndpoints P pp guess response starts
  let pk : GXMSS.PublicKey PP H := ⟨GXMSS.IntervalMerkle.root P I pp endpoints fillers, pp⟩
  let (forgery, history) ← runWithSigningKernel
    (intervalSplicedSign P enc K I pp guess response starts endpoints fillers)
    (A.forge pk) emptyHistory
  pure (pk, forgery, history)

private theorem chainSpliceView_eq_context [SampleableType R]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : SchemeAdversary PP H M R h v) (pp : PP) (guess : Guess h w v)
    (response : H) (starts : Epoch h → Fin v → H) (fillers : Fillers I H) :
    chainSpliceView P enc K I A pp guess response starts fillers =
      (fun result : Result PP H M R h v =>
        ((result.pk, result.forgery, result.history) : ExperimentResult
          (GXMSS.PublicKey PP H) (Epoch h) M (GXMSS.Signature R H h v))) <$>
      runContextSpliced P enc K (intervalChainContext P I fillers) A pp guess response starts := by
  simp only [chainSpliceView, runContextSpliced, intervalSplicedSign,
    intervalChainContext, map_bind, map_pure]
  rfl

private theorem intervalSplicedSigningOracle_used [SampleableType R]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (pp : PP) (guess : Guess h w v) (response : H) (starts endpoints : Epoch h → Fin v → H)
    (fillers : Fillers I H) (history : History (Epoch h) M (GXMSS.Signature R H h v))
    (ep : Epoch h) (msg first : M) (signature : Option (GXMSS.Signature R H h v))
    (hused : history ep = some (first, signature)) :
    intervalSplicedSigningOracle P enc K I pp guess response starts endpoints fillers
      (ep, msg) history = pure (none, history) := by
  exact signingKernelOracle_used _ history ep msg first signature hused

private theorem intervalSplicedSigningOracle_inactive [SampleableType R]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (pp : PP) (guess : Guess h w v) (response : H) (starts endpoints : Epoch h → Fin v → H)
    (fillers : Fillers I H) (history : History (Epoch h) M (GXMSS.Signature R H h v))
    (ep : Epoch h) (msg : M) (hfresh : history ep = none) (hinactive : ¬ Epoch.IsActive I ep) :
    intervalSplicedSigningOracle P enc K I pp guess response starts endpoints fillers
      (ep, msg) history = pure (none, Function.update history ep (some (msg, none))) := by
  unfold intervalSplicedSigningOracle
  rw [signingKernelOracle_unused _ _ _ _ hfresh]
  simp [intervalSplicedSign, contextSplicedSign, intervalChainContext, hinactive]
  rfl

private theorem intervalSplicedSigningOracle_active [SampleableType R]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (pp : PP) (guess : Guess h w v) (response : H) (starts endpoints : Epoch h → Fin v → H)
    (fillers : Fillers I H) (history : History (Epoch h) M (GXMSS.Signature R H h v))
    (ep : Epoch h) (msg : M) (hfresh : history ep = none) (hactive : Epoch.IsActive I ep) :
    intervalSplicedSigningOracle P enc K I pp guess response starts endpoints fillers
      (ep, msg) history = (do
        let wr ← enc.retry ($ᵗ R) pp msg ep K
        let signature := wr.map
          (intervalSplicedSignatureOfWord P I pp guess response starts endpoints fillers ep)
        pure (signature, Function.update history ep (some (msg, signature)))) := by
  unfold intervalSplicedSigningOracle
  rw [signingKernelOracle_unused _ _ _ _ hfresh]
  simp [intervalSplicedSign, contextSplicedSign, intervalChainContext, hactive, monad_norm]
  rfl

private theorem intervalSplicedSigningOracle_zero [SampleableType R]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (I : Interval h)
    (pp : PP) (guess : Guess h w v) (response : H) (starts endpoints : Epoch h → Fin v → H)
    (fillers : Fillers I H) (history : History (Epoch h) M (GXMSS.Signature R H h v))
    (ep : Epoch h) (msg : M) (hfresh : history ep = none) :
    intervalSplicedSigningOracle P enc 0 I pp guess response starts endpoints fillers
      (ep, msg) history = pure (none, Function.update history ep (some (msg, none))) := by
  unfold intervalSplicedSigningOracle
  rw [signingKernelOracle_unused _ _ _ _ hfresh]
  by_cases hactive : Epoch.IsActive I ep <;>
    simp [intervalSplicedSign, contextSplicedSign, intervalChainContext, hactive,
      IncomparableEncoding.retry] <;> rfl

private theorem intervalSplicedSignatureOfWord_honest
    (P : HashInstance PP T X H h w v) (I : Interval h) (pp : PP)
    (guess : Guess h w v) (starts : Epoch h → Fin v → H) (fillers : Fillers I H)
    (ep : Epoch h) (wr : Codeword v (2 ^ w) × R) :
    intervalSplicedSignatureOfWord P I pp guess
      (P.chain pp (guessedEpoch guess) (guessedChain guess) 0
        ((guessedPosition guess).val + 1) (starts (guessedEpoch guess) (guessedChain guess)))
      starts (GXMSS.endpoints P pp starts) fillers ep wr =
    GXMSS.Interval.signatureOfWord P I
      ⟨⟨pp, starts, GXMSS.endpoints P pp starts⟩, fillers⟩ ep wr := by
  have hots : (fun i => splicedChainValue P pp guess
      (P.chain pp (guessedEpoch guess) (guessedChain guess) 0
        ((guessedPosition guess).val + 1) (starts (guessedEpoch guess) (guessedChain guess)))
      starts ep i (wr.1 i)) = (fun i => P.chain pp ep i 0 (wr.1 i) (starts ep i)) := by
    funext i
    exact splicedChainValue_honest P pp guess starts ep i _
  simp only [intervalSplicedSignatureOfWord, GXMSS.Interval.signatureOfWord,
    GXMSS.signatureOfWord, hots]

private theorem intervalSplicedSign_honest
    [SampleableType R]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (pp : PP) (guess : Guess h w v) (starts : Epoch h → Fin v → H)
    (fillers : Fillers I H) :
    intervalSplicedSign P enc K I pp guess
      (P.chain pp (guessedEpoch guess) (guessedChain guess) 0
        ((guessedPosition guess).val + 1) (starts (guessedEpoch guess) (guessedChain guess)))
      starts (GXMSS.endpoints P pp starts) fillers =
    GXMSS.Interval.sign P enc K I
      ⟨⟨pp, starts, GXMSS.endpoints P pp starts⟩, fillers⟩  := by
  funext ep msg
  have hsig : (contextSplicedSignatureOfWord (R := R) P (intervalChainContext P I fillers) pp guess
      (P.chain pp (guessedEpoch guess) (guessedChain guess) 0
        ((guessedPosition guess).val + 1) (starts (guessedEpoch guess) (guessedChain guess)))
      starts (GXMSS.endpoints P pp starts) ep) =
      GXMSS.Interval.signatureOfWord P I
        ⟨⟨pp, starts, GXMSS.endpoints P pp starts⟩, fillers⟩ ep := by
    funext wr
    exact intervalSplicedSignatureOfWord_honest P I pp guess starts fillers ep wr
  dsimp only [intervalSplicedSign, contextSplicedSign]
  rw [hsig]
  simp only [intervalChainContext, GXMSS.Interval.sign, decide_eq_true_eq]

private theorem intervalSplicedSigningOracle_honest
    [SampleableType H] [SampleableType R] [DecidableEq H]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (pp : PP) (guess : Guess h w v) (starts : Epoch h → Fin v → H)
    (fillers : Fillers I H) :
    intervalSplicedSigningOracle P enc K I pp guess
      (P.chain pp (guessedEpoch guess) (guessedChain guess) 0
        ((guessedPosition guess).val + 1) (starts (guessedEpoch guess) (guessedChain guess)))
      starts (GXMSS.endpoints P pp starts) fillers =
    signingOracle (GXMSS.Interval.scheme P enc K I)
      ⟨⟨pp, starts, GXMSS.endpoints P pp starts⟩, fillers⟩  := by
  exact congrArg signingKernelOracle (intervalSplicedSign_honest P enc K I pp guess starts fillers)

/-- An honest cut response gives the entire original fixed-key interval interaction,
including the public key, adaptive output, failed/repeated requests and final history. -/
theorem chainSpliceView_honest [SampleableType H] [SampleableType R] [DecidableEq H]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : Adversary unifSpec (GXMSS.PublicKey PP H) (Epoch h) M (GXMSS.Signature R H h v))
    (pp : PP) (guess : Guess h w v) (starts : Epoch h → Fin v → H) (fillers : Fillers I H) :
    let (epoch, chain, position) := guess
    chainSpliceView P enc K I A pp guess
      (P.chain pp epoch chain 0 (position.val + 1) (starts epoch chain)) starts fillers =
        GXMSS.Interval.viewFromKeys P enc K I A pp starts fillers := by
  rcases guess with ⟨epoch, chain, position⟩
  have hend := splicedEndpoints_honest P pp (epoch, chain, position) starts
  have hkernel := intervalSplicedSign_honest P enc K I pp
    (epoch, chain, position) starts fillers
  simp only [guessedEpoch, guessedChain, guessedPosition] at hend hkernel
  simp only [chainSpliceView, hend, hkernel, GXMSS.Interval.viewFromKeys,
    GXMSS.Interval.viewWithKeys, GXMSS.Interval.keys, GXMSS.keys]
  rfl

/-- Every successful record in a replacement interaction retains its exact retry witness. -/
private theorem chainSpliceView_successful_record_signature
     [SampleableType R]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : SchemeAdversary PP H M R h v) (pp : PP) (guess : Guess h w v)
    (response : H) (starts : Epoch h → Fin v → H) (fillers : Fillers I H)
    (out : ExperimentResult (GXMSS.PublicKey PP H) (Epoch h) M (GXMSS.Signature R H h v))
    (hout : out ∈ support (chainSpliceView P enc K I A pp guess response starts fillers))
    (ep : Epoch h) (msg : M) (sig : GXMSS.Signature R H h v)
    (hrecord : let (_, _, history) := out; history ep = some (msg, some sig)) :
    ∃ wr, sig = intervalSplicedSignatureOfWord P I pp guess response starts
        (splicedEndpoints P pp guess response starts) fillers ep wr ∧
      enc.value pp msg wr.2 ep = some wr.1 := by
  classical
  unfold ExperimentResult at out
  rw [chainSpliceView_eq_context] at hout
  change out ∈ MonadAttach.support
    ((fun result : Result PP H M R h v => (result.pk, result.forgery, result.history)) <$>
      runContextSpliced P enc K (intervalChainContext P I fillers) A pp guess response starts)
    at hout
  simp only [MonadAttach.support_map, Set.mem_image] at hout
  obtain ⟨result, hresult, rfl⟩ := hout
  obtain ⟨wr, hsig, hvalue⟩ := runContextSpliced_successful_record_signature P enc K
    (intervalChainContext P I fillers) A pp guess response starts result hresult ep msg sig hrecord
  exact ⟨wr, hsig, hvalue⟩

private theorem intervalSign_full [SampleableType R]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (sk : GXMSS.Interval.SecretKey PP H h v I) (ep : Epoch h) (msg : M)
    (sig : GXMSS.Signature R H h v)
    (hs : some sig ∈ support (GXMSS.Interval.sign P enc K I sk ep msg)) :
    ∃ wr, sig = GXMSS.Interval.signatureOfWord P I sk ep wr ∧
      enc.value sk.complete.seed msg wr.2 ep = some wr.1 := by
  unfold GXMSS.Interval.sign at hs
  split at hs
  · simp only [support_map, Set.mem_image] at hs
    obtain ⟨answer, hanswer, heq⟩ := hs
    cases answer with
    | none => simp at heq
    | some wr =>
      refine ⟨wr, ?_, IncomparableEncoding.Retry.value_eq_some_of_mem_retry enc
        ($ᵗ R) sk.complete.seed msg ep K wr.1 wr.2 hanswer⟩
      simpa using heq.symm
  · simp at hs

private theorem viewFromKeys_successful_record_signature
    [SampleableType H] [SampleableType R] [DecidableEq H]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : SchemeAdversary PP H M R h v) (pp : PP)
    (starts : Epoch h → Fin v → H) (fillers : Fillers I H)
    (out : ExperimentResult (GXMSS.PublicKey PP H) (Epoch h) M (GXMSS.Signature R H h v))
    (hout : out ∈ support (GXMSS.Interval.viewFromKeys P enc K I A pp starts fillers))
    (ep : Epoch h) (msg : M) (sig : GXMSS.Signature R H h v)
    (hrecord : let (_, _, history) := out; history ep = some (msg, some sig)) :
    ∃ wr, sig = GXMSS.Interval.signatureOfWord P I
        (GXMSS.Interval.keys P I pp starts fillers).2 ep wr ∧
      enc.value pp msg wr.2 ep = some wr.1 := by
  unfold GXMSS.Interval.viewFromKeys GXMSS.Interval.viewWithKeys at hout
  rw [mem_support_bind_iff] at hout
  obtain ⟨⟨forgery, history⟩, hrun, hreturn⟩ := hout
  subst out
  exact runWithSigningOracle_preserves_successfulHistorySatisfies
    (GXMSS.Interval.scheme P enc K I) (GXMSS.Interval.keys P I pp starts fillers).2
    (fun ep msg sig => ∃ wr,
      sig = GXMSS.Interval.signatureOfWord P I (GXMSS.Interval.keys P I pp starts fillers).2
        ep wr ∧ enc.value pp msg wr.2 ep = some wr.1)
    (intervalSign_full P enc K I (GXMSS.Interval.keys P I pp starts fillers).2)
    (A.forge _) emptyHistory (successfulHistorySatisfies_empty _) _ hrun ep msg sig hrecord

private theorem intervalSplicedSignatureOfWord_selected
    (P : HashInstance PP T X H h w v) (I : Interval h) (pp : PP)
    (guess : Guess h w v) (response : H) (starts endpoints : Epoch h → Fin v → H)
    (fillers : Fillers I H) (wr : Codeword v (2 ^ w) × R)
    (hword : (wr.1 (guessedChain guess)).val = (guessedPosition guess).val + 1) :
    let signature := intervalSplicedSignatureOfWord P I pp guess response starts endpoints
      fillers (guessedEpoch guess) wr
    signature.ots (guessedChain guess) = response := by
  rcases guess with ⟨epoch, chain, position⟩
  dsimp only [guessedEpoch, guessedChain, guessedPosition] at hword ⊢
  simp [intervalSplicedSignatureOfWord, splicedChainValue,
    guessedEpoch, guessedChain, guessedPosition, hword]

private theorem intervalSplicedEndpoints_terminal
    (P : HashInstance PP T X H h w v) (pp : PP)
    (guess : Guess h w v) (response : H) (starts : Epoch h → Fin v → H)
    (hfinal : (guessedPosition guess).val + 1 = 2 ^ w - 1) :
    splicedEndpoints P pp guess response starts (guessedEpoch guess) (guessedChain guess) =
      response := splicedEndpoints_guess_final P pp guess response starts hfinal

end GXMSS.Interval.Reductions
