/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
-- frontier: CslibFrontier.Crypto.Computational.DiffieHellman

public import Examples.ElGamal.ComputationalComplexity
public import VCVioFrontier.Examples.ElGamal.Reduction
public import VCVioFrontier.Examples.ElGamal.Transport
public import VCVioFrontier.CryptoFoundations.Asymptotics
public import VCVioFrontier.OracleComp.Realization

/-!
# The advantage of VCVio's one-time ElGamal adversary under uniform machine DDH

A pair of uniform word procedures implements a typed adversary when it preserves the joint law
of the selected messages and saved state and the guessing law on encoded ciphertexts. These two
local conditions connect the original typed DDH reduction to the compiled distinguisher.
-/

public section

namespace VCVioFrontier.ElGamal

open Turing.MultiTapeTM Cslib.Crypto OracleComp
open PFunctor.FreeM (MachineRealization)
open scoped ENNReal NNReal

variable (F : PrimeOrderGroupFamily)

/-- Sample a uniform group element by transporting a uniform exponent through the generator. -/
@[instance_reducible] noncomputable def carrierSampler (d : F.Desc) :
    SampleableType (F.Carrier d) :=
  SampleableType.ofEquiv (Equiv.ofBijective _ (F.smul_generator_bijective d))

attribute [local instance] carrierSampler

/-- VCVio's algebraic ElGamal, specialized to the field and group selected by `d`. -/
noncomputable abbrev typedScheme (d : F.Desc) :=
  elGamalAsymmEnc (ZMod (F.order d)) (F.Carrier d) (F.generator d)

variable (desc : ℕ → F.Desc)

/-- Each security parameter selects one typed two-stage adversary; its state type may vary. -/
abbrev TypedAdversary := (n : ℕ) → (typedScheme F (desc n)).IND_CPA_OneTime_Adversary

/-- The same two word procedures implement every member of the typed family. Their certificates
charge the entire saved state. VCVio selects the first message on `true`; frontier selects the
second one, so the encoded choice reverses the two positions. -/
structure AdversaryRealization (adv : TypedAdversary F desc) where
  /-- One two-stage word program for the family. -/
  words : Encryption.WordAdversary
  /-- Strict uniform machine certificates for both procedures. -/
  efficient : words.IsPPT
  /-- The representation of the state shared by the stages. -/
  state : (n : ℕ) → (adv n).State ↪ List Bool
  /-- Message selection preserves the joint law of both messages and the state. -/
  choose (n : ℕ) (u : F.Carrier (desc n)) :
    Cslib.ProbComp.eval (words.choose n (encPair F.encDesc encBits (desc n, F.encode _ u))) =
      (Cslib.ProbComp.eval ((adv n).chooseMessages u)).map
        (encodeChoice (F.encode _) (state n))
  /-- Guessing preserves the output law on the state and ciphertext sent by the reduction. -/
  guess (n : ℕ) (st : (adv n).State) (v w : F.Carrier (desc n)) :
    Cslib.ProbComp.eval (words.guess n (state n st)
      (encPair encBits encBits (F.encode _ v, F.encode _ w))) =
      Cslib.ProbComp.eval ((adv n).distinguish st (v, w))

variable {F desc} {adv : TypedAdversary F desc}

/-- The machine and clock compiled from the two procedures and their shared reduction program. -/
noncomputable def AdversaryRealization.machine (R : AdversaryRealization F desc adv) :
    MachineRealization (runRequest R.words) F.encDDHInput encBool (reductionSource F) :=
  PFunctor.FreeM.MachineRealization.ofPPTProgram (reductionSource_realized F R.efficient)

/-- The named typed reduction has the same output law as the compiled word implementation on
all encoded DDH challenges. -/
theorem AdversaryRealization.eval_reduction (R : AdversaryRealization F desc adv) (n : ℕ)
    (u v w : F.Carrier (desc n)) :
    Cslib.ProbComp.eval (elGamalAsymmEnc.IND_CPA_OneTime_DDHReduction (adv n)
      (F.generator (desc n)) u v w) =
    Cslib.ProbComp.eval (ddhReduction F R.words n (desc n) u v w) := by
  rw [ddhReduction_eq]
  exact eval_reductionBody (F.encode (desc n)) (R.state n) (fun p q => F.add (desc n, p, q))
    (encPair encBits encBits) ((adv n).chooseMessages u) (adv n).distinguish _ _ v w
    (R.choose n u) (R.guess n) (F.add_encode (desc n))

/-- Closing the original VCVio open reduction with its two-stage adversary and fair-coin
handlers gives the output law of the three-request word implementation. -/
theorem AdversaryRealization.eval_openOracle (R : AdversaryRealization F desc adv) (n : ℕ)
    (u v w : F.Carrier (desc n)) :
    Cslib.ProbComp.eval (simulateQ (elGamalAsymmEnc.oneTimeINDCPAImpl (adv n) +
      elGamalAsymmEnc.oneTimeDDHFairCoinImpl)
      (elGamalAsymmEnc.IND_CPA_OneTime_DDHReduction_openOracle (State := (adv n).State)
        (F.generator (desc n)) u v w)) =
      Cslib.ProbComp.eval (ddhReduction F R.words n (desc n) u v w) := by
  rw [elGamalAsymmEnc.IND_CPA_OneTime_DDHReduction_openOracle_eval, R.eval_reduction]

/-- At its certified clock the named machine outputs exactly the encoded result of VCVio's
original open reduction with its two-stage adversary and independent fair coin installed. -/
theorem AdversaryRealization.machine_output_openOracle (R : AdversaryRealization F desc adv)
    (n : ℕ) (u v w : F.Carrier (desc n)) :
    R.machine.output ⟨⟨n, desc n, u, v⟩, w⟩ =
      (Cslib.ProbComp.eval (simulateQ (elGamalAsymmEnc.oneTimeINDCPAImpl (adv n) +
        elGamalAsymmEnc.oneTimeDDHFairCoinImpl)
        (elGamalAsymmEnc.IND_CPA_OneTime_DDHReduction_openOracle (State := (adv n).State)
          (F.generator (desc n)) u v w))).map encBool := by
  rw [R.eval_openOracle]
  exact R.machine.encoded_law ⟨⟨n, desc n, u, v⟩, w⟩

/-- One finite-control probabilistic machine realizes the named typed reduction at all parameters
and every supported branch halts within one polynomial, even on noncanonical input words. -/
theorem AdversaryRealization.exists_halting_machine (R : AdversaryRealization F desc adv) :
    ∃ (k : ℕ) (State : Type) (_ : Finite State) (M : Turing.MultiTapePTM k Bool State) (c e : ℕ),
      (∀ n (u v w : F.Carrier (desc n)),
        let input := F.encDDHInput ⟨⟨n, desc n, u, v⟩, w⟩
        (Cslib.ProbComp.eval (simulateQ (elGamalAsymmEnc.oneTimeINDCPAImpl (adv n) +
          elGamalAsymmEnc.oneTimeDDHFairCoinImpl)
          (elGamalAsymmEnc.IND_CPA_OneTime_DDHReduction_openOracle (State := (adv n).State)
            (F.generator (desc n)) u v w))).map encBool =
          Cslib.ProbComp.eval (M.runClosed (c * (input.length + 1) ^ e) input)) ∧
      ∀ word, ∀ final ∈ (Cslib.ProbComp.eval (M.runConfigFrom (Cslib.ProbComp.uniform Bool)
        Empty.elim (c * (word.length + 1) ^ e) (M.initialConfig word))).support,
        final.tapes.state = none := by
  let M := R.machine
  refine ⟨M.tapes, M.State, M.finiteState, M.machine, M.coefficient, M.degree, ?_, M.halts⟩
  intro n u v w
  exact (R.machine_output_openOracle n u v w).symm

/-- The real and random typed DDH experiments agree separately with the corresponding games
under the point setup law. Their exponents are sampled exactly uniformly. -/
theorem AdversaryRealization.ddh_games (R : AdversaryRealization F desc adv) (n : ℕ) :
    Cslib.ProbComp.eval (DiffieHellman.ddhRealExperiment (F.generator (desc n))
      (elGamalAsymmEnc.IND_CPA_OneTime_DDHReduction (adv n))) =
      F.ddhRealGame (fun k => PMF.pure (desc k)) (ddhReduction F R.words) n ∧
    Cslib.ProbComp.eval (DiffieHellman.ddhRandomExperiment (F.generator (desc n))
      (elGamalAsymmEnc.IND_CPA_OneTime_DDHReduction (adv n))) =
      F.ddhRandomGame (fun k => PMF.pure (desc k)) (ddhReduction F R.words) n := by
  constructor <;> simp only [PrimeOrderGroupFamily.ddhRealGame, PrimeOrderGroupFamily.ddhRandomGame,
    Game.withSetup_pure, Cslib.Crypto.eval_ddhRealExperiment, Cslib.Crypto.eval_ddhRandomExperiment,
    DiffieHellman.ddhRealExperiment, DiffieHellman.ddhRandomExperiment, Cslib.ProbComp.eval_bind,
    eval_uniformSample, R.eval_reduction]

/-- VCVio's exact factor of two, with the uniform machine distinguisher in both DDH games. -/
theorem AdversaryRealization.advantage_eq (R : AdversaryRealization F desc adv) (n : ℕ) :
    (typedScheme F (desc n)).IND_CPA_OneTime_Advantage ProbCompRuntime.probComp (adv n) =
      2 * (Game.advantage
        (F.ddhRealGame (fun k => PMF.pure (desc k)) (ddhReduction F R.words) n)
        (F.ddhRandomGame (fun k => PMF.pure (desc k)) (ddhReduction F R.words) n) : ℝ≥0∞) := by
  rw [elGamalAsymmEnc.elGamal_oneTime_advantage_eq_two_mul_ddhAdvantage
    (F.smul_generator_bijective (desc n)) (adv n), DiffieHellman.ddhAdvantage,
    evalDist_eq_toMeasure, evalDist_eq_toMeasure, boolDist_toMeasure_eq_advantage,
    (R.ddh_games n).1, (R.ddh_games n).2]

/-- One-time IND-CPA security of the typed family against adversaries with uniform two-stage
implementations, under the ordinary strict uniform machine DDH assumption. -/
theorem AdversaryRealization.negligible_advantage (R : AdversaryRealization F desc adv)
    (hDDH : F.DDH (fun k => PMF.pure (desc k))) :
    negligible (fun n => (typedScheme F (desc n)).IND_CPA_OneTime_Advantage
      ProbCompRuntime.probComp (adv n)) := by
  simp only [R.advantage_eq]
  apply negligible_const_mul _ (by norm_num)
  apply (negligible_coe_iff _).2
  exact hDDH (ddhReduction F R.words) (ddhReduction_isPPT F R.efficient)

end VCVioFrontier.ElGamal
