/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module

public import VCVio.CryptoFoundations.ChallengeVerifyProtocol.Kilian
public import VCVio.CryptoFoundations.VectorCommitment.OnlineExtraction

/-!
# Soundness of the Kilian transformation in the random-oracle model

Kilian's protocol is an *argument*: a prover that can find two openings of one commitment to
different values can cheat, so soundness cannot hold against unbounded provers for a fixed hash
function. This file states and proves soundness in the random-oracle model, where the commitment's
oracle `X →ₒ Y` is a lazily sampled random function shared by the cheating prover and the
verifier's check.

A cheating prover is a two-phase `DetVectorCommitment.OnlineAdversary` whose challenge is the PCP's
coins: it outputs a commitment, receives the coins, and outputs claimed values together with an
opening proof. The Kilian verifier accepts when the commitment's check accepts the opening and the
PCP verifier, replayed against the claims, accepts (`PCP.kilianDecision`).
`KilianTransformation.romAcceptance` is the probability of acceptance, run from the empty cache.

## Main result

`KilianTransformation_rom_sound`: for every statement outside the language, every cheating prover
`P` and every extractor `extract`,

`romAcceptance ≤ ε + onlineExtractionError extract P`,

where `ε` is the soundness error of the PCP and the online extraction error of the commitment is
measured against the cheating prover itself. The proof is the classical one: the extractor reads a
proof string off the oracle cache when the commitment is output, before the coins are drawn. If an
accepted response agrees with that proof string, the PCP verifier accepts it
(`runVerifier_of_kilianDecision`), which PCP soundness bounds by `ε` over the independent coins
(`DetVectorCommitment.prEvent_onlineRun_le`); otherwise the run is an online extraction failure.

The bound holds for every extractor, so the best extractor for the commitment gives the tightest
bound. Bounding the online extraction error of a concrete commitment, such as a Merkle tree, in
terms of the prover's query count is a separate theorem about that commitment.
-/

public section

open OracleComp OracleSpec DetVectorCommitment

open scoped NNReal ENNReal

namespace KilianTransformation

variable {Stmt Wit : Type} {X Y Cm Td Pf : Type} [DecidableEq X] [SampleableType Y]

/-- The probability that the Kilian verifier for statement `x` accepts against the cheating prover
`P` in the random-oracle model: `P` commits, the verifier draws the PCP's coins, `P` responds with
claimed values and an opening proof, and the verifier accepts iff the commitment's check accepts the
opening and the PCP verifier's replay against the claims accepts (`PCP.kilianDecision`). -/
@[expose]
noncomputable def romAcceptance (pcp : PCP Stmt Wit)
    (vc : DetVectorCommitment X Y pcp.Symbol Cm Td Pf pcp.length) (x : Stmt) {St : Type}
    (P : OnlineAdversary X Y Cm St pcp.Coins (PartialVec pcp.length pcp.Symbol × Pf)) : ℝ≥0∞ :=
  Pr{let t ← vc.onlineRun pcp.sampleCoins P}[
    pcp.kilianDecision x t.chal t.resp.1 t.accepted = true]

end KilianTransformation

open KilianTransformation

variable {Stmt Wit : Type} {X Y Cm Td Pf : Type} [DecidableEq X] [SampleableType Y]

/-- **Soundness of the Kilian transformation in the random-oracle model.** If the PCP is sound with
error `ε`, then for every statement `x` outside the language, every cheating prover `P` and every
extractor `extract`, the Kilian verifier accepts with probability at most `ε` plus the online
extraction error of `extract` against `P` itself. -/
theorem KilianTransformation_rom_sound (pcp : PCP Stmt Wit) (rel : Stmt → Wit → Bool)
    (vc : DetVectorCommitment X Y pcp.Symbol Cm Td Pf pcp.length)
    (extract : (X →ₒ Y).QueryCache → Cm → Fin pcp.length → pcp.Symbol)
    {ε : ℝ≥0} (hpcp : pcp.soundness rel ε) (x : Stmt) (hx : ¬ ∃ w, rel x w) {St : Type}
    (P : OnlineAdversary X Y Cm St pcp.Coins (PartialVec pcp.length pcp.Symbol × Pf)) :
    romAcceptance pcp vc x P ≤ ε + vc.onlineExtractionError extract pcp.sampleCoins P := by
  unfold romAcceptance onlineExtractionError
  -- The PCP verifier accepts the extracted proof string on the drawn coins.
  let good : OnlineTranscript X Y Cm pcp.Coins (PartialVec pcp.length pcp.Symbol × Pf) → Prop :=
    fun t => pcp.runVerifier x t.chal (List.Vector.ofFn (extract t.cache t.cm)) = true
  refine (prEvent_le_prEvent_add_prEvent_and_not _ _ good).trans (add_le_add ?_ ?_)
  · -- The extracted proof string is fixed before the coins, so PCP soundness bounds this event.
    refine prEvent_onlineRun_le vc pcp.sampleCoins P
      (fun cm cache coins =>
        pcp.runVerifier x coins (List.Vector.ofFn (extract cache cm)) = true) fun cm cache => ?_
    have h := hpcp x hx (List.Vector.ofFn (extract cache cm))
    simp only [bind_pure_comp, prEvent_map] at h
    exact h
  · -- An accepted response that the PCP verifier rejects on the extracted string disagrees with it.
    refine prEvent_mono _ _ _ fun t ⟨hacc, hbad⟩ => ⟨?_, fun hagree => hbad ?_⟩
    · unfold PCP.kilianDecision at hacc
      exact (Bool.and_eq_true _ _).mp hacc |>.1
    · exact runVerifier_of_kilianDecision pcp x t.chal t.resp.1 t.accepted _
        ((claimsAgree_iff _ _).mp hagree) hacc
