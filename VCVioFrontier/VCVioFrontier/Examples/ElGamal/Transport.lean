/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
-- frontier: CslibFrontier.Languages.Probabilistic.Basic

public import Examples.ElGamal.Basic
public import VCVioFrontier.Examples.ElGamal.Choice
public import VCVioFrontier.OracleComp.Measure

/-!
# Transport of the two stages of the ElGamal reduction

Jointly transporting both messages and the saved state through the first stage preserves the
output law of the complete reduction whenever guessing agrees on each resulting ciphertext.
-/

public section

namespace VCVioFrontier.ElGamal

/-- Transport the actual reduction body across group and state representations. The Boolean
returned by the experiment tests the adversary's guess against the independent challenge bit. -/
theorem eval_reductionBody {G St : Type} [AddCommGroup G]
    (encode : G → List Bool) (state : St → List Bool)
    (add : List Bool → List Bool → List Bool) (pair : List Bool × List Bool → List Bool)
    (choose : _root_.ProbComp (G × G × St)) (guess : St → G × G → _root_.ProbComp Bool)
    (chooseWord : Cslib.ProbComp ((List Bool × List Bool) × List Bool))
    (guessWord : List Bool → List Bool → Cslib.ProbComp Bool) (v w : G)
    (hchoose : Cslib.ProbComp.eval chooseWord = (Cslib.ProbComp.eval choose).map
      (encodeChoice encode state))
    (hguess : ∀ st p q, Cslib.ProbComp.eval (guessWord (state st) (pair (encode p, encode q))) =
      Cslib.ProbComp.eval (guess st (p, q)))
    (hadd : ∀ p q, add (encode p) (encode q) = encode (p + q)) :
    Cslib.ProbComp.eval (elGamalAsymmEnc.oneTimeDDHReductionBody choose ($ᵗ Bool) guess v w) =
      Cslib.ProbComp.eval (elGamalAsymmEnc.oneTimeDDHReductionWith chooseWord
        (Cslib.ProbComp.uniform Bool) fun c bit =>
          let (first, second, st) := oneTimeChoice id c
          guessWord st (pair (encode v, add (encode w) (if bit then first else second)))) := by
  simp only [elGamalAsymmEnc.oneTimeDDHReductionBody, elGamalAsymmEnc.oneTimeDDHReductionWith,
    Cslib.ProbComp.eval_bind,
    Cslib.ProbComp.eval_pure, eval_uniformSample, Cslib.ProbComp.eval_uniform, hchoose,
    PMF.bind_map]
  apply congrArg (PMF.bind _)
  funext ⟨first, second, st⟩
  apply congrArg (PMF.bind _)
  funext b
  cases b <;> simp [hadd, hguess]

end VCVioFrontier.ElGamal
