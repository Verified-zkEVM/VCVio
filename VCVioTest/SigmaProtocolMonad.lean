/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.CryptoFoundations.FiatShamir.Sigma

/-! # A Σ-protocol whose prover queries an oracle

`ChallengeVerifyProtocol` and `SigmaProtocol` take the participants' monad as a parameter. These
checks instantiate it with `OracleComp coinSpec`, so the prover and the simulator flip coins
through an oracle rather than computing in `ProbComp`. The protocol commits to a coin and answers
with the challenge, and the verifier accepts exactly when the response equals the challenge.

The checks state perfect completeness and special soundness in that monad, and run the protocol
through the Fiat-Shamir transform, whose Σ-protocol monad only has to lift into the signature
scheme's monad.
-/

public section

open OracleComp OracleSpec

namespace SigmaProtocolMonadTest

/-- A Σ-protocol in `OracleComp coinSpec`: commit to a coin, answer with the challenge. -/
@[expose]
def protocol : SigmaProtocol (OracleComp coinSpec) Unit Unit Bool Unit Bool Bool
    (fun _ _ => true) where
  commit _ _ := do
    let b ← coin
    pure (b, ())
  respond _ _ _ chal := pure chal
  verify _ _ chal resp := resp == chal
  sim _ := coin
  extract _ _ _ _ := pure ()

/-- The honest prover convinces the verifier on every challenge, in the coin-oracle monad. -/
theorem protocol_perfectlyComplete : protocol.PerfectlyComplete := by
  intro x w _ ω
  have h : (do
      let (pc, sc) ← protocol.commit x w
      let π ← protocol.respond x w sc ω
      return protocol.verify x pc ω π : OracleComp coinSpec Bool) =
      (fun _ => true) <$> coin := by
    simp [protocol, map_eq_bind_pure_comp]
  rw [h, OracleComp.evalDist_map_const]
  simp

/-- The same prover with a verifier that rejects the honest response. -/
@[expose]
def rejecting : SigmaProtocol (OracleComp coinSpec) Unit Unit Bool Unit Bool Bool
    (fun _ _ => true) :=
  { protocol with verify := fun _ _ chal resp => resp != chal }

/-- Completeness is not vacuous in the coin-oracle monad: the rejecting verifier fails it. -/
theorem rejecting_not_perfectlyComplete : ¬ rejecting.PerfectlyComplete := by
  intro hc
  have h : (do
      let (pc, sc) ← rejecting.commit () ()
      let π ← rejecting.respond () () sc true
      return rejecting.verify () pc true π : OracleComp coinSpec Bool) =
      (fun _ => false) <$> coin := by
    simp [rejecting, protocol, map_eq_bind_pure_comp]
  have h1 := hc () () rfl true
  rw [h, OracleComp.evalDist_map_const] at h1
  simp at h1

/-- The protocol is specially sound: its relation holds for every witness. -/
theorem protocol_speciallySound : protocol.SpeciallySound := by
  intro x pc ω₁ π₁ ω₂ π₂ _ _ _ w _
  rfl

/-- The relation's sole instance and witness. -/
@[expose]
def relation : GenerableRelation Unit Unit (fun _ _ => true) where
  gen := pure ((), ())
  gen_sound := by simp

/-- Fiat-Shamir accepts the coin-oracle prover: its monad lifts into the signature scheme's,
which adds uniform sampling and the hash oracle. -/
example : SignatureAlg (OracleComp (unifSpec + coinSpec + (Unit × Bool →ₒ Bool)))
    (M := Unit) (PK := Unit) (SK := Unit) (S := Bool × Bool) :=
  FiatShamir protocol relation Unit

end SigmaProtocolMonadTest
