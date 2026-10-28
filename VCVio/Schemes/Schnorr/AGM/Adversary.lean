/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kobi Gurkan, Quang Dao
-/

module
public import VCVio.CryptoFoundations.GroupModel.Interaction
public import VCVio.Schemes.Schnorr.Signature
public import VCVio.OracleComp.Traversal

/-! # Algebraic Schnorr adversaries

Hash requests explain their commitment before receiving a scalar challenge. Signing replies
extend the received group basis by one commitment. The initial inputs are the generator and
public key, in that order. Erasure forwards requests to the existing Schnorr signature game.

The full-field nonce convention is that of Fuchsbauer, Plouviez and Seurin,
*Blind Schnorr Signatures and Signed ElGamal Encryption in the Algebraic Group Model*,
EUROCRYPT 2020, https://eprint.iacr.org/2019/877.
-/

public section

open OracleComp OracleSpec GroupModel.Interaction

namespace Schnorr.AGM

/-- Schnorr has one additive group sort. -/
abbrev Group (G : Type) := fun _ : Unit => G

/-- Plain query data; hash commitments travel in the explained group argument. -/
inductive Request (M : Type) where
  /-- Private uniform sampling. -/
  | random (n : ℕ)
  /-- Hash a message with its separately supplied commitment. -/
  | hash (m : M)
  /-- Request a signature on a message. -/
  | sign (m : M)

/-- Hash replies and signature responses are scalars; commitments are group inputs. -/
@[expose] def Reply (F M : Type) : Request M → Type
  | .random n => Fin (n + 1)
  | .hash _ => F
  | .sign _ => F

/-- The generator and public key supplied as the first two received group elements. -/
@[expose] def initial {G : Type} (g pk : G) : Message Unit (Group G) :=
  ⟨(), fun _ => [g, pk]⟩

/-- A scalar answer contributes no group inputs. -/
@[expose] def scalarReply {F G : Type} (z : F) : Message F (Group G) :=
  ⟨z, fun _ => []⟩

/-- A signing answer contributes its commitment to the received basis. -/
@[expose] def signingReply {F G : Type} (R : G) (z : F) : Message F (Group G) :=
  ⟨z, fun _ => [R]⟩

/-- Hash requests carry exactly one commitment; other requests carry no group arguments. -/
@[expose] def RequestShape {F M G : Type} (q : Explained F (Request M) (Group G)) : Prop :=
  match q.value.data with
  | .hash _ => (q.value.groups ()).length = 1
  | _ => q.value.groups () = []

/-- The existing signature game's oracle family, including signing queries. -/
abbrev rawSpec (F M G : Type) := (unifSpec + (M × G →ₒ F)) + (M →ₒ G × F)

/-- Forward well-shaped requests to the original Schnorr oracles. The protocol certificate
excludes the default commitment used to make malformed requests total. -/
@[expose] def oracle {F M G : Type} [Zero G] :
    QueryImpl (plainSpec (Group G) (Request M) (Reply F M))
      (OracleComp (rawSpec F M G)) := by
  intro ⟨q, groups⟩
  cases q with
  | random n => exact do
      let r ← (rawSpec F M G).query (.inl (.inl n))
      pure ⟨r, fun _ => []⟩
  | hash m => exact do
      let c ← (rawSpec F M G).query (.inl (.inr (m, (groups ()).headD 0)))
      pure (scalarReply c)
  | sign m => exact do
      let sig ← (rawSpec F M G).query (.inr m)
      pure (signingReply sig.1 sig.2)

/-- Decode a final message, commitment, and scalar response. -/
@[expose] def forgery {F M G : Type} [Zero G]
    (out : Explained F (M × F) (Group G)) : M × (G × F) :=
  (out.value.data.1, (out.value.groups ()).headD 0, out.value.data.2)

end Schnorr.AGM

namespace Schnorr

/-- An algebraic Schnorr adversary with protocol shape certified on every reply path. -/
structure AlgebraicAdversary (F G M : Type) [Field F] [AddCommGroup G] [Module F G]
    extends GroupModel.Interaction.Adversary F (AGM.Group G) Unit (AGM.Request M)
      (AGM.Reply F M) (M × F) where
  /-- Hash requests and final outputs contain exactly one commitment. -/
  protocol : ∀ input, allPathsSatisfy AGM.RequestShape
    (fun out => (out.value.groups ()).length = 1) (fun _ => Set.univ) (main input)

/-- Forget explanations and forward sampling, hashing, and signing to the existing
`Schnorr.signature` unforgeability game without modifying any of its oracles. -/
@[expose] def AlgebraicAdversary.toUnforgeableAdversary {F G M : Type}
    [Field F] [SampleableType F] [AddCommGroup G] [Module F G] [DecidableEq G]
    [SampleableType G] [DecidableEq M] (A : AlgebraicAdversary F G M) (g : G) :
    SignatureAlg.UnforgeableAdversary (signature F G g M) where
  main pk := AGM.forgery <$> simulateQ (fun q => AGM.oracle q.value) (A.main (AGM.initial g pk))

end Schnorr
