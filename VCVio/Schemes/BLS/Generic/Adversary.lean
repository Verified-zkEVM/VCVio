/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.CryptoFoundations.GroupModel.Game
public import VCVio.CryptoFoundations.GroupModel.Instances
public import VCVio.Schemes.BLS.AGM.Adversary

/-! # Generic BLS adversaries in Type 3 pairing groups

The shared handle interface supplies group operations, private coins, and hash and signing
requests. Encodings carry only unit, so they disclose no group values. Each game reply
installs a fresh first-source handle, including replies to repeated requests. The real
interpretation uses the existing BLS signature experiment and its shared random oracle.
-/

public section

open OracleComp OracleSpec GroupModel GroupModel.Interaction

namespace BLS.Generic

variable {F M G₁ G₂ : Type}

/-- The algebraic source family inherits its componentwise commutative addition. -/
instance sourceAddCommMonoid [AddCommGroup G₁] [AddCommGroup G₂] (b : Bool) :
    AddCommMonoid (AGM.Group G₁ G₂ b) where
  toAddMonoid := inferInstance
  add_comm := by cases b <;> exact add_comm

/-- Each algebraic source sort inherits its scalar module structure. -/
instance sourceModule [Semiring F] [AddCommGroup G₁] [Module F G₁]
    [AddCommGroup G₂] [Module F G₂] (b : Bool) : Module F (AGM.Group G₁ G₂ b) where
  smul := (· • ·)
  one_smul := by cases b <;> exact one_smul F
  mul_smul := by cases b <;> exact mul_smul
  smul_zero := by cases b <;> exact smul_zero
  smul_add := by cases b <;> exact smul_add
  add_smul := by cases b <;> exact add_smul
  zero_smul := by cases b <;> exact zero_smul F

/-- Source equality is decided using the corresponding real group. -/
instance sourceDecidableEq [DecidableEq G₁] [DecidableEq G₂] :
    ∀ b, DecidableEq (AGM.Group G₁ G₂ b)
  | false => inferInstanceAs (DecidableEq G₁)
  | true => inferInstanceAs (DecidableEq G₂)

/-- Hash and signing requests are distinguished by the two summands. -/
abbrev Query (M : Type) := M ⊕ M

/-- A generic BLS program uses the shared pairing handle interface with trivial encodings. -/
abbrev Adversary (F M : Type) :=
  HandleAdversary F pairingSig (fun _ => Unit) Unit (Query M) (fun _ => Unit) M

/-- The oracle signature of a generic BLS program, including its private coins. -/
abbrev adversarySpec (F M : Type) :=
  spec F pairingSig + (encSpec (fun _ : PSort => Unit) +
    (unifSpec + handleSpec (S := PSort) (Query M) (fun _ => Unit)))

/-- BLS requests contain only message data and the final output is one signature handle. -/
@[expose] def FollowsProtocol {F M : Type} (A : Adversary F M) : Prop :=
  ∀ input, allPathsSatisfy
    (fun q => match q with
      | .inr (.inr (.inr q)) => ∀ s, q.groups s = []
      | _ => True)
    (fun out => (out.groups .g₁).length = 1 ∧ out.groups .g₂ = [] ∧ out.groups .gₜ = [])
    (fun _ => Set.univ) (A input)

/-- A query counts toward the adversary's direct hash budget. -/
@[expose] def isHash {F M : Type} : (adversarySpec F M).Domain → Prop
  | .inr (.inr (.inr ⟨.inl _, _⟩)) => True
  | _ => False

/-- A query counts toward the adversary's signing budget. -/
@[expose] def isSign {F M : Type} : (adversarySpec F M).Domain → Prop
  | .inr (.inr (.inr ⟨.inr _, _⟩)) => True
  | _ => False

/-- Hash-budget membership is decidable from the query constructor. -/
instance isHashDecidable : DecidablePred (isHash (F := F) (M := M)) := fun q => by
  unfold isHash
  split <;> infer_instance

/-- Signing-budget membership is decidable from the query constructor. -/
instance isSignDecidable : DecidablePred (isSign (F := F) (M := M)) := fun q => by
  unfold isSign
  split <;> infer_instance

/-- Initial tables contain the two generators and the corresponding public-key components. -/
@[expose] def initialInput {G₁ G₂ Gₜ : Type} (g₁ : G₁) (g₂ : G₂) (pk : G₁ × G₂) :
    Message Unit (PFam G₁ G₂ Gₜ) :=
  ⟨(), fun | .g₁ => [g₁, pk.1] | .g₂ => [g₂, pk.2] | .gₜ => []⟩

/-- Forward hash and signing requests to the BLS oracles and expose their replies as points. -/
@[expose] def oracle {M G₁ G₂ Gₜ : Type} :
    QueryImpl (plainSpec (PFam G₁ G₂ Gₜ) (Query M) (fun _ => Unit))
      (OracleComp (AGM.rawSpec M G₁)) :=
  fun q => do
    let v ← match q.data with
      | .inl m => (AGM.rawSpec M G₁).query (.inl (.inr m))
      | .inr m => (AGM.rawSpec M G₁).query (.inr m)
    return ⟨(), fun | .g₁ => [v] | .g₂ => [] | .gₜ => []⟩

/-- Interpret handle operations in the real pairing model and decode the signature handle.
The hash and signing effects are forwarded to the ordinary BLS security experiment. -/
@[expose] def Adversary.toUnforgeableAdversary {F M G₁ G₂ Gₜ : Type}
    [Field F] [SampleableType F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ] [DecidableEq Gₜ]
    [∀ s, DecidableEq (PFam G₁ G₂ Gₜ s)]
    (A : Adversary F M) (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₁ : G₁) (g₂ : G₂) :
    SignatureAlg.UnforgeableAdversary (scheme (M := M) e g₁ g₂) where
  main pk := (fun z =>
    let out := lookupMessage z.2 z.1
    (out.data, (out.groups .g₁).headD 0)) <$>
      HandleAdversary.run A (pairingReal e) (fun _ _ => ())
        (QueryImpl.ofLift unifSpec (OracleComp (AGM.rawSpec M G₁))) oracle
        (initialInput g₁ g₂ pk)

end BLS.Generic
