/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Schemes.Proximity.Basic
public import VCVio.CryptoFoundations.GroupModel.Interaction
public import VCVio.OracleComp.Traversal
public import VCVio.OracleComp.QueryTracking.QueryBound

/-! # Certified algebraic adversaries for Proximity

The initial group inputs are the first-source generator and the second-source generator and
public key. Each hash or signing reply adds one first-source input. Query arguments carry
only ordinary data; a forgery carries exactly one first-source point. Forgetting explanations
forwards the same requests and returns the same message and signature to `SignatureAlg`.
-/

public section

open OracleComp OracleSpec GroupModel.Interaction

namespace Proximity.AGM

/-- The two pairing source groups are tracked separately, even for equal carrier types. -/
abbrev Group (G₁ G₂ : Type) : Bool → Type
  | false => G₁
  | true => G₂

/-- Addition is inherited separately in each source sort. -/
instance {G₁ G₂ : Type} [AddMonoid G₁] [AddMonoid G₂] (s : Bool) :
    AddMonoid (Group G₁ G₂ s) := by cases s <;> dsimp [Group] <;> infer_instance

/-- Scalar multiplication is inherited separately in each source sort. -/
instance {F G₁ G₂ : Type} [SMul F G₁] [SMul F G₂] (s : Bool) :
    SMul F (Group G₁ G₂ s) := by cases s <;> dsimp [Group] <;> infer_instance

/-- A pair of chronological lists, one for each source group. -/
@[expose] def groupInputs {G₁ G₂ : Type} (xs : List G₁) (ys : List G₂) :
    Groups (Group G₁ G₂)
  | false => xs
  | true => ys

/-- Requests distinguish randomness, base hashes, and signatures. -/
abbrev Query (F Slot : Type) (dimension : ℕ) :=
  (ℕ ⊕ Index Slot dimension) ⊕ Proximity.Message F Slot dimension

/-- Randomness is ordinary reply data; hash and signature replies carry group points. -/
@[expose] def Reply {F Slot : Type} {dimension : ℕ} : Query F Slot dimension → Type
  | .inl (.inl n) => Fin (n + 1)
  | _ => Unit

/-- The direct scheme's ambient and signing oracles. -/
abbrev rawSpec (F Slot G₁ : Type) (dimension : ℕ) :=
  (unifSpec + (Index Slot dimension →ₒ G₁)) + (Proximity.Message F Slot dimension →ₒ G₁)

/-- Both generators and the second-source public key are explicit received inputs. -/
@[expose] def initialInput {G₁ G₂ : Type} (g₁ : G₁) (g₂ pk : G₂) :
    GroupModel.Interaction.Message Unit (Group G₁ G₂) :=
  ⟨(), groupInputs [g₁] [g₂, pk]⟩

/-- Forward ordinary requests, delivering hash and signature values as received group points. -/
@[expose] def oracle {F Slot G₁ G₂ : Type} {dimension : ℕ} :
    QueryImpl (plainSpec (Group G₁ G₂) (Query F Slot dimension) Reply)
      (OracleComp (rawSpec F Slot G₁ dimension)) := by
  intro ⟨q, _⟩
  rcases q with ((n | i) | m)
  · exact do
      let r ← (rawSpec F Slot G₁ dimension).query (.inl (.inl n))
      return ⟨r, groupInputs [] []⟩
  · exact do
      let h ← (rawSpec F Slot G₁ dimension).query (.inl (.inr i))
      return ⟨(), groupInputs [h] []⟩
  · exact do
      let σ ← (rawSpec F Slot G₁ dimension).query (.inr m)
      return ⟨(), groupInputs [σ] []⟩

/-- Decode the forged message and the first signature point. -/
@[expose] def forgery {F Slot G₁ G₂ : Type} [Zero G₁] {dimension : ℕ}
    (out : Explained F (Proximity.Message F Slot dimension) (Group G₁ G₂)) :
    Proximity.Message F Slot dimension × G₁ :=
  (out.value.data, (out.value.groups false).headD 0)

/-- Direct adversarial base-hash requests count toward the hash budget. -/
@[expose] def isHash {F Slot : Type} {dimension : ℕ} : Query F Slot dimension → Bool
  | .inl (.inr _) => true
  | _ => false

/-- Signing requests count toward the signing budget. -/
@[expose] def isSign {F Slot : Type} {dimension : ℕ} : Query F Slot dimension → Bool
  | .inr _ => true
  | _ => false

end Proximity.AGM

namespace Proximity

/-- A certified interactive algebraic adversary with the Proximity message and output protocol. -/
structure AlgebraicAdversary (F Slot G₁ G₂ : Type) (dimension : ℕ) {Gₜ : Type} [Field F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ]
    (_e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (_g₁ : G₁) (_g₂ : G₂) extends
    GroupModel.Interaction.Adversary F (AGM.Group G₁ G₂) Unit
      (AGM.Query F Slot dimension) AGM.Reply (Message F Slot dimension) where
  /-- Requests have no group arguments; a forgery contains one first-source signature point. -/
  protocol : ∀ input, allPathsSatisfy
    (fun q => ∀ s, q.value.groups s = [])
    (fun out => (out.value.groups false).length = 1 ∧ out.value.groups true = [])
    (fun _ => Set.univ) (main input)

/-- Execute the certified program against the direct scheme's raw oracle interface. -/
@[expose] def AlgebraicAdversary.rawMain {F Slot G₁ G₂ Gₜ : Type} {dimension : ℕ}
    [Field F] [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ]
    {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₁ : G₁} {g₂ : G₂}
    (A : AlgebraicAdversary F Slot G₁ G₂ dimension e g₁ g₂) (pk : G₂) :
    OracleComp (AGM.rawSpec F Slot G₁ dimension)
      (Explained F (Message F Slot dimension) (AGM.Group G₁ G₂)) :=
  simulateQ (fun q => AGM.oracle q.value) (A.main (AGM.initialInput g₁ g₂ pk))

/-- Forget explanations by forwarding the original requests and returning the decoded forgery. -/
@[expose] def AlgebraicAdversary.toUnforgeableAdversary {F Slot G₁ G₂ Gₜ : Type}
    {dimension : ℕ} [Field F] [SampleableType F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ] [DecidableEq Gₜ]
    {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₁ : G₁} {g₂ : G₂}
    (A : AlgebraicAdversary F Slot G₁ G₂ dimension e g₁ g₂) :
    SignatureAlg.UnforgeableAdversary (scheme (Slot := Slot) (dimension := dimension) e g₂) where
  main pk := AGM.forgery <$> A.rawMain pk

/-- Explicit pathwise bounds on the raw adversary's hash and signing requests at every key. -/
@[expose] def AlgebraicAdversary.QueryBound {F Slot G₁ G₂ Gₜ : Type} {dimension : ℕ}
    [Field F] [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ]
    {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₁ : G₁} {g₂ : G₂}
    (A : AlgebraicAdversary F Slot G₁ G₂ dimension e g₁ g₂) (qh qs : ℕ) : Prop :=
  ∀ pk, IsQueryBoundP (A.rawMain pk) (fun q => AGM.isHash q = true) qh ∧
    IsQueryBoundP (A.rawMain pk) (fun q => AGM.isSign q = true) qs

end Proximity
