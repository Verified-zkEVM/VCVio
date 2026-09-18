/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.CryptoFoundations.SigmaProtocol
import VCVio.OracleComp.EvalDist.Measure

/-!
# Restricting the challenge space of a Σ-protocol

A challenge map changes the verifier's challenge policy while keeping the commitment and
response algorithms. Completeness and unique responses survive any map; special soundness
requires injectivity, since the original extractor needs distinct original challenges.
Full-transcript simulation requires a separate argument for the new challenge distribution.
-/

public section

open OracleComp OracleSpec

variable {Stmt Wit Commit PrvState Chal Resp C D : Type} {rel : Stmt → Wit → Bool}

namespace ChallengeVerifyProtocol

/-- Interpret challenges through `encode`, retaining the original commitment algorithm. -/
@[expose]
def restrictChallenges
    (σ : ChallengeVerifyProtocol Stmt Wit Commit PrvState Chal Resp rel) (encode : C → Chal) :
    ChallengeVerifyProtocol Stmt Wit Commit PrvState C Resp rel where
  commit := σ.commit
  respond x w s c := σ.respond x w s (encode c)
  verify x pc c p := σ.verify x pc (encode c) p

@[simp] theorem restrictChallenges_id
    (σ : ChallengeVerifyProtocol Stmt Wit Commit PrvState Chal Resp rel) :
    σ.restrictChallenges id = σ := rfl

@[simp] theorem restrictChallenges_comp
    (σ : ChallengeVerifyProtocol Stmt Wit Commit PrvState Chal Resp rel)
    (encode : C → Chal) (encode' : D → C) :
    (σ.restrictChallenges encode).restrictChallenges encode' =
      σ.restrictChallenges (encode ∘ encode') := rfl

/-- Perfect completeness makes every supported honest response valid for every challenge. -/
theorem PerfectlyComplete.verify [SampleableType Chal]
    {σ : ChallengeVerifyProtocol Stmt Wit Commit PrvState Chal Resp rel}
    (hc : σ.PerfectlyComplete) (x : Stmt) (w : Wit) (hrel : rel x w = true)
    (pc : Commit) (sc : PrvState) (hpc : (pc, sc) ∈ support (σ.commit x w))
    (c : Chal) (p : Resp) (hp : p ∈ support (σ.respond x w sc c)) :
    σ.verify x pc c p = true := by
  apply (evalDist_apply_setOf_eq_one_iff_forall_mem_support _ (· = true)).mp (hc x w hrel)
  rw [mem_support_bind_iff]
  refine ⟨(pc, sc), hpc, ?_⟩
  rw [mem_support_bind_iff]
  refine ⟨c, mem_support_uniformSample Chal, ?_⟩
  rw [mem_support_bind_iff]
  exact ⟨p, hp, by simp⟩

/-- Uniform challenge restriction preserves perfect completeness, including non-surjective maps. -/
theorem PerfectlyComplete.restrictChallenges [SampleableType Chal] [SampleableType C]
    {σ : ChallengeVerifyProtocol Stmt Wit Commit PrvState Chal Resp rel}
    (hc : σ.PerfectlyComplete) (encode : C → Chal) :
    (σ.restrictChallenges encode).PerfectlyComplete := by
  intro x w hrel
  apply (evalDist_apply_setOf_eq_one_iff_forall_mem_support _ (· = true)).mpr
  intro b hb
  simp only [mem_support_bind_iff, mem_support_pure_iff] at hb
  obtain ⟨⟨pc, sc⟩, hpc, c, _, p, hp, rfl⟩ := hb
  exact hc.verify x w hrel pc sc hpc (encode c) p hp

/-- Restricting challenges cannot create two responses to a single original challenge. -/
theorem UniqueResponses.restrictChallenges
    {σ : ChallengeVerifyProtocol Stmt Wit Commit PrvState Chal Resp rel}
    (hur : σ.UniqueResponses) (encode : C → Chal) :
    (σ.restrictChallenges encode).UniqueResponses :=
  fun x pc c p₁ p₂ => hur x pc (encode c) p₁ p₂

end ChallengeVerifyProtocol

namespace SigmaProtocol

/-- Restrict the interaction and feed encoded challenges to the same named extractor.
The commitment-only `sim` field is retained; this does not assert full-transcript HVZK. -/
@[expose]
def restrictChallenges
    (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel) (encode : C → Chal) :
    SigmaProtocol Stmt Wit Commit PrvState C Resp rel where
  toChallengeVerifyProtocol := σ.toChallengeVerifyProtocol.restrictChallenges encode
  sim := σ.sim
  extract c₁ p₁ c₂ p₂ := σ.extract (encode c₁) p₁ (encode c₂) p₂

@[simp] theorem restrictChallenges_id
    (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel) :
    σ.restrictChallenges id = σ := rfl

@[simp] theorem restrictChallenges_comp
    (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel)
    (encode : C → Chal) (encode' : D → C) :
    (σ.restrictChallenges encode).restrictChallenges encode' =
      σ.restrictChallenges (encode ∘ encode') := rfl

/-- An injective challenge restriction preserves the original witness extraction guarantee. -/
theorem SpeciallySoundAt.restrictChallenges
    {σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel} {x : Stmt}
    (hss : σ.SpeciallySoundAt x) (encode : C → Chal) (hinj : Function.Injective encode) :
    (σ.restrictChallenges encode).SpeciallySoundAt x := by
  intro pc c₁ c₂ p₁ p₂ hne hv₁ hv₂ w hw
  exact hss pc (encode c₁) (encode c₂) p₁ p₂ (hinj.ne hne) hv₁ hv₂ w hw

/-- Injective challenge restriction preserves special soundness at every statement. -/
theorem SpeciallySound.restrictChallenges
    {σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel}
    (hss : σ.SpeciallySound) (encode : C → Chal) (hinj : Function.Injective encode) :
    (σ.restrictChallenges encode).SpeciallySound :=
  fun x => (hss x).restrictChallenges encode hinj

end SigmaProtocol
