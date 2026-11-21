/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVioFrontier.Examples.ElGamal.Bound
import CslibFrontier.Tactic.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair.Projections

/-! # Stateful installations of the honest ElGamal programs and the two-stage adversary -/

public section

namespace VCVioFrontierTest.ElGamal

open VCVioFrontier.ElGamal Turing.MultiTapeTM Cslib.Crypto Cslib.Probability

variable (F : PrimeOrderGroupFamily) (desc : ℕ → F.Desc)

private def drawTape : PFunctor.Handler (StateM (List ℕ)) (Honest.signature F) :=
  fun _ tape => (tape.headD 0, tape.tail)

/-- Installing a tape of exponents consumes the first for key generation and the second
for encryption, preserves the rest and decrypts to the original encoded group element. -/
example (n a b : ℕ) (rest : List ℕ) (m : F.Carrier (desc n)) :
    let msg := F.encode (desc n) m
    let source : (Honest.signature F).FreeM _ := do
      let keys ← Honest.keygen F desc n
      let ct ← Honest.encrypt F desc n keys.1 msg
      let out ← Honest.decrypt F desc n keys.2 ct
      return (keys, ct, out)
    let keys := (Honest.keygen F desc n).liftM (Honest.fixedExponent F a)
    let ct := (Honest.encrypt F desc n keys.1 msg).liftM (Honest.fixedExponent F b)
    ((source.liftM (drawTape F)).run (a :: b :: rest)) = ((keys, ct, some msg), rest) := by
  dsimp only
  rw [← Honest.decrypt_encrypt_fixedExponent F desc n a b m]
  simp only [PFunctor.FreeM.liftM_bind, PFunctor.FreeM.liftM_pure, Honest.decrypt, Honest.encrypt,
    Honest.keygen, PFunctor.FreeM.liftM_map, Honest.liftM_exponent]
  rfl

/-- Select zero and the public key, saving the public key for comparison. -/
@[expose] noncomputable def typed : TypedAdversary F desc := fun n => {
  State := F.Carrier (desc n)
  chooseMessages := fun pk => pure (0, pk, pk)
  distinguish := fun st ct => pure (decide (ct.2 = st))
}

/-- Encoded procedures for the same adversary. -/
@[expose] noncomputable def words : Encryption.WordAdversary where
  choose n pk := pure ((dropFrame pk, F.encode (desc n) 0), dropFrame pk)
  guess _ st ct := pure (decide (dropFrame ct = st))

/-- The word procedures realize the typed stateful adversary. -/
noncomputable def realization (hd : ComputableInPolyTime desc encUnary F.encDesc) :
    AdversaryRealization F desc (typed F desc) where
  words := words F desc
  efficient := by
    constructor
    · apply IsPPTOn.isPPT
      apply ComputableInPolyTime.isPPTOn
      change ComputableInPolyTime
        (fun p : ℕ × List Bool => ((dropFrame p.2, F.encode (desc p.1) 0), dropFrame p.2)) _ _
      polytime
    · apply ComputableInPolyTime.isPPTOn
      change ComputableInPolyTime (fun p : ℕ × List Bool × List Bool =>
        decide (dropFrame p.2.2 = p.2.1)) _ _
      polytime
  state n := ⟨F.encode (desc n), F.encode_injective (desc n)⟩
  choose := by
    intro n u
    simp [words, typed]
    rfl
  guess := by
    intro n st v w
    change F.Carrier (desc n) at st
    simp only [words, typed, Cslib.ProbComp.eval_pure, dropFrame_encPair_encBits]
    change PMF.pure (decide (F.encode _ w = F.encode _ st)) = PMF.pure (decide (w = st))
    exact congrArg PMF.pure (decide_eq_decide.mpr (F.encode_injective _).eq_iff)

/-- The stateful procedure is admissible for the machine-grounded security theorem. -/
theorem secure (hd : ComputableInPolyTime desc encUnary F.encDesc)
    (hDDH : F.DDH (fun n => PMF.pure (desc n))) :
    negligible fun n => (typedScheme F (desc n)).IND_CPA_OneTime_Advantage
      ProbCompRuntime.probComp (typed F desc n) :=
  (realization F desc hd).negligible_advantage hDDH

/-- The same adversary is admissible against the implemented bounded-coin scheme. -/
theorem implemented_secure (hd : ComputableInPolyTime desc encUnary F.encDesc)
    (hDDH : F.DDH (fun n => PMF.pure (desc n))) :
    negligible fun n => (wordScheme F desc n).IND_CPA_OneTime_Advantage
      ProbCompRuntime.probComp (implementedAdversary F desc (words F desc) n) :=
  implemented_secureAgainst hDDH (words F desc) ⟨typed F desc, realization F desc hd, rfl⟩

end VCVioFrontierTest.ElGamal
