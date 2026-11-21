/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVioFrontier.Examples.ElGamal.Reduction

/-! # Two challenge-bit branches of VCVio's ElGamal reduction -/

public section

namespace VCVioFrontierTest.ElGamal

/-- Two distinct challenge messages and a saved state. -/
@[expose] def choose : _root_.ProbComp (ℤ × ℤ × ℤ) := pure (2, 7, 13)

/-- The distinguisher checks that the saved state, first ciphertext component and masked message
all survived the reduction. With this challenge it identifies the first message. -/
@[expose] def guess (st : ℤ) (ct : ℤ × ℤ) : _root_.ProbComp Bool :=
  pure (decide (st = 13 ∧ ct = (3, 7)))

/-- The first message produces the ciphertext checked by the adversary. -/
theorem distinguishFirst : Cslib.ProbComp.eval (elGamalAsymmEnc.oneTimeDDHReductionBody
    choose (pure true) guess 3 5) = PMF.pure true := by
  simp [elGamalAsymmEnc.oneTimeDDHReductionBody, elGamalAsymmEnc.oneTimeDDHReductionWith,
    choose, guess]

/-- The second message produces a different ciphertext and the guess is false. -/
theorem distinguishSecond : Cslib.ProbComp.eval (elGamalAsymmEnc.oneTimeDDHReductionBody
    choose (pure false) guess 3 5) = PMF.pure true := by
  simp [elGamalAsymmEnc.oneTimeDDHReductionBody, elGamalAsymmEnc.oneTimeDDHReductionWith,
    choose, guess]

open VCVioFrontier.ElGamal Cslib.Crypto Turing.MultiTapeTM PFunctor

/-- Supply distinct group messages and a fixed false bit. Guess true exactly when the expected
saved state and the encryption of the zero message both arrive at the second stage. -/
private noncomputable def wrongGuess (F : PrimeOrderGroupFamily) (d : F.Desc) :
    Handler Id signature
  | .choose .. => ((F.encode d 0, F.encode d (F.generator d)), [true, false])
  | .coin => false
  | .guess _ st ct =>
    decide (st = [true, false] ∧ ct = encPair encBits encBits (F.encode d 0, F.encode d 0))

/-- With zero DDH components the encoded false-branch challenge is the zero message.
The guess is true, so the actual reduction reports a loss. -/
example (F : PrimeOrderGroupFamily) (n : ℕ) (d : F.Desc) :
    (reductionSource F ⟨⟨n, d, 0, 0⟩, 0⟩).liftM (wrongGuess F d) = false := by
  have h (q : Request) : (FreeM.lift (P := signature) q).liftM (wrongGuess F d) =
      wrongGuess F d q := FreeM.liftM_lift _ _
  simp only [reductionSource, elGamalAsymmEnc.oneTimeDDHReductionWith, FreeM.liftM_bind,
    h, FreeM.liftM_pure]
  change (false == decide (_ ∧ _ = _)) = false
  simp [challenge, oneTimeChoice, wrongGuess, F.add_encode]

end VCVioFrontierTest.ElGamal
