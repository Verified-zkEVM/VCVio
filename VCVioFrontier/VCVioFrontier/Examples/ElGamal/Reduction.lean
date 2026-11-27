/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
-- frontier: CslibFrontier.Crypto.Computational.ElGamal

public import CslibFrontier.Crypto.Computational.ElGamal
public import PolyFunFrontier.PFunctor.Free.Realization
public import Examples.ElGamal.Basic
public import VCVioFrontier.Examples.ElGamal.Choice
import CslibFrontier.Tactic.PPT

/-!
# The one-time ElGamal reduction as a program with three requests

The distinguisher receives a DDH tuple, calls the adversary to obtain messages and saved state,
flips its own fair challenge bit and calls the adversary again. Both adversary stages run under
one family of machine certificates. The program returns whether the adversary guessed the bit.
-/

public section

namespace VCVioFrontier.ElGamal

open Turing.MultiTapeTM Cslib.Crypto Cslib.Probability PFunctor

/-- The three operations of the encoded reduction. -/
inductive Request where
  | choose (n : ℕ) (pk : List Bool)
  | coin
  | guess (n : ℕ) (state ct : List Bool)

/-- The first response contains both challenge messages and the saved adversary state. -/
abbrev signature : PFunctor := ⟨Request, fun
  | .choose _ _ => Encryption.ChoiceOut (List Bool)
  | .coin | .guess .. => Bool⟩

/-- Close the adversary ports with their installed procedures and the coin port with a fair bit. -/
@[expose] noncomputable def runRequest (adv : Encryption.WordAdversary) :
    Handler Cslib.ProbComp signature
  | .choose n pk => adv.choose n pk
  | .coin => Cslib.ProbComp.uniform Bool
  | .guess n st ct => adv.guess n st ct

variable (F : PrimeOrderGroupFamily)

/-- Public key passed to message selection on the first component of a DDH tuple. -/
@[expose] def publicKey (x : F.DDHInput) : List Bool :=
  encPair F.encDesc encBits (x.groupParameters, F.encode x.groupParameters x.leftPublic)

/-- Mask the selected message by the third DDH element and frame the ciphertext. -/
@[expose] def challenge (x : F.DDHInput) (choice : Encryption.ChoiceOut (List Bool))
    (b : Bool) : List Bool :=
  let (first, second, _) := oneTimeChoice id choice
  encPair encBits encBits (F.encode x.groupParameters x.rightPublic,
    F.add (x.groupParameters, F.encode x.groupParameters x.candidateShared,
      if b then first else second))

/-- Encoded one-time DDH reduction, with separate message selection, coin and guess requests. -/
@[expose] def reductionSource (x : F.DDHInput) : signature.FreeM Bool :=
  elGamalAsymmEnc.oneTimeDDHReductionWith
    (FreeM.lift (P := signature) (Request.choose x.secParam (publicKey F x)))
    (FreeM.lift (P := signature) Request.coin)
    fun choice b => FreeM.lift (P := signature)
      (Request.guess x.secParam (Encryption.ChoiceOut.state choice) (challenge F x choice b))

/-- The source tree interpreted by the word adversary and independent fair coins. -/
@[expose] noncomputable def ddhReduction (adv : Encryption.WordAdversary) : F.DDHDistinguisher :=
  fun n d u v w => (reductionSource F ⟨⟨n, d, u, v⟩, w⟩).liftM (runRequest adv)

/-- Operational equation for the implemented distinguisher, exposing the saved word and challenge
bit in the order in which the original adversary procedures observe them. -/
theorem ddhReduction_eq (adv : Encryption.WordAdversary) (n : ℕ) (d : F.Desc)
    (u v w : F.Carrier d) : ddhReduction F adv n d u v w = (do
      let choice ← adv.choose n (encPair F.encDesc encBits (d, F.encode d u))
      let b ← Cslib.ProbComp.uniform Bool
      let (first, second, state) := oneTimeChoice id choice
      let g ← adv.guess n state (encPair encBits encBits (F.encode d v,
        F.add (d, F.encode d w, if b then first else second)))
      return b == g) := by
  have h (q : Request) :
      (FreeM.lift (P := signature) q).liftM (runRequest adv) = runRequest adv q :=
    FreeM.liftM_lift (P := signature) (runRequest adv) q
  simp only [ddhReduction, reductionSource, elGamalAsymmEnc.oneTimeDDHReductionWith,
    FreeM.liftM_bind, h, FreeM.liftM_pure]
  rfl

/-- For a fixed hidden bit the encoded challenge is exactly that of frontier's typed-message
reducer. Mixing the fixed-bit games also compares the guess with the actual challenge bit. -/
theorem eval_ddhReduction_fixedBits (adv : Encryption.WordAdversary) (n : ℕ) (d : F.Desc)
    (u v w : F.Carrier d) :
    Cslib.ProbComp.eval (ddhReduction F adv n d u v w) =
      (Cslib.Probability.PMF.uniformOfFintype Bool).bind fun bit =>
        (Cslib.ProbComp.eval (F.elGamalMsgToDDHDistinguisher (fun _ _ _ _ => true)
          (fun _ m => m) adv bit n d u v w)).map (fun out => bit == out) := by
  rw [ddhReduction_eq]
  simp only [oneTimeChoice, id_eq, PrimeOrderGroupFamily.elGamalMsgToDDHDistinguisher,
    PrimeOrderGroupFamily.elGamalMsgToDDHDistinguisherWith, ite_true,
    Cslib.ProbComp.eval_bind, Cslib.ProbComp.eval_pure, Cslib.ProbComp.eval_uniform, PMF.map_bind]
  exact PMF.bind_comm _ _ _

/-- Sampling and both calls, including copying the saved state and computing the challenge
ciphertext, admit one uniform source realization for all inputs. -/
theorem reductionSource_realized {adv : Encryption.WordAdversary} (hA : adv.IsPPT) :
    FreeM.PPTProgram (runRequest adv) F.encDDHInput encBool (reductionSource F) := by
  let E := encPair F.encDDHInput (Encryption.encChoiceOut encBits)
  let EB := encPair E encBool
  have hpk : ComputableInPolyTime (publicKey F) F.encDDHInput encBits :=
    ((F.encDDHInput_groupParameters_polyTime .id').prod
      (F.encDDHInput_leftPublic_polyTime .id')).encoding_comp
  have hc := hA.choose.on.preprocess
    (prepare := fun x : F.DDHInput => (x.secParam, publicKey F x))
    ((F.encDDHInput_secParam_polyTime .id').prod hpk)
  have hchoose : FreeM.PPTProgram (runRequest adv) F.encDDHInput (Encryption.encChoiceOut encBits)
      (fun x => FreeM.lift (P := signature) (Request.choose x.secParam (publicKey F x))) := by
    simpa only [id_map] using FreeM.PPTProgram.call
      (H := runRequest adv)
      (query := fun x : F.DDHInput => Request.choose x.secParam (publicKey F x))
      (answer := fun _ => id) (by simpa only [runRequest, id_map] using hc)
  have hcoin : FreeM.PPTProgram (runRequest adv) E encBool
      (fun _ => FreeM.lift (P := signature) Request.coin) := by
    simpa only [id_map] using FreeM.PPTProgram.call (H := runRequest adv)
      (query := fun _ : F.DDHInput × Encryption.ChoiceOut (List Bool) => Request.coin)
      (answer := fun _ => id) (by
        simp only [runRequest, id_map]
        ppt)
  let mkInput := fun p : (F.DDHInput × Encryption.ChoiceOut (List Bool)) × Bool =>
    (p.1.1.secParam, p.1.2.2, challenge F p.1.1 p.1.2 p.2)
  have hx : ComputableInPolyTime
      (fun p : (F.DDHInput × Encryption.ChoiceOut (List Bool)) × Bool => p.1.1) EB F.encDDHInput :=
    (ComputableInPolyTime.fst _ _).comp (ComputableInPolyTime.fst E encBool)
  have hd := F.encDDHInput_groupParameters_polyTime hx
  have hv := F.encDDHInput_rightPublic_polyTime hx
  have hw := F.encDDHInput_candidateShared_polyTime hx
  have hct : ComputableInPolyTime
      (fun p : (F.DDHInput × Encryption.ChoiceOut (List Bool)) × Bool =>
        challenge F p.1.1 p.1.2 p.2) EB encBits := by
    unfold challenge oneTimeChoice
    apply ComputableInPolyTime.encoding_comp
    exact hv.prod (F.computableInPolyTime_add.comp (hd.prod (hw.prod (by
      dsimp [EB, E]; polytime))))
  have hprepare : ComputableInPolyTime mkInput EB Encryption.encGuessInput := by
    dsimp only [mkInput, Encryption.encGuessInput]
    apply ComputableInPolyTime.prod
    · exact F.encDDHInput_secParam_polyTime hx
    · exact (by dsimp [EB, E]; fun_prop : ComputableInPolyTime
        (fun p : (F.DDHInput × Encryption.ChoiceOut (List Bool)) × Bool => p.1.2.2)
        EB encBits).prod hct
  have hguess : FreeM.PPTProgram (runRequest adv) EB encBool
      (fun p => FreeM.lift (P := signature)
        (Request.guess p.1.1.secParam p.1.2.2 (challenge F p.1.1 p.1.2 p.2))) := by
    simpa only [id_map] using FreeM.PPTProgram.call (H := runRequest adv)
      (query := fun p : (F.DDHInput × Encryption.ChoiceOut (List Bool)) × Bool =>
        Request.guess p.1.1.secParam p.1.2.2 (challenge F p.1.1 p.1.2 p.2))
      (answer := fun _ => id) (by
        simpa only [runRequest, id_map, mkInput] using hA.guess.preprocess hprepare)
  unfold reductionSource
  apply hchoose.bindWith
  apply hcoin.bindWith
  apply hguess.bindWith
  apply FreeM.PPTProgram.localMap
  dsimp [EB, E]
  polytime

/-- The compiled open source implements a strict uniform DDH distinguisher. -/
theorem ddhReduction_isPPT {adv : Encryption.WordAdversary} (hA : adv.IsPPT) :
    (ddhReduction F adv).IsPPT :=
  (reductionSource_realized F hA).isPPTOn

end VCVioFrontier.ElGamal
