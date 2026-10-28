/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.GroupModel.Interaction
public import VCVio.Schemes.BLS.Basic
public import VCVio.OracleComp.Traversal

/-! # Algebraic BLS adversaries

The shared interactive algebraic group model tracks the two source groups separately.
Initially the adversary receives both generators and both public-key components. Hash and
signing replies each add one first-source-group input. Oracle arguments are ordinary data;
a protocol certificate requires outgoing query group lists to be empty. The final output has
exactly one first-source-group point and no second-source-group points.
-/

public section

open OracleComp OracleSpec GroupModel.Interaction

namespace BLS.AGM

/-- The two source groups, indexed separately even when their carrier types coincide. -/
abbrev Group (G₁ G₂ : Type) : Bool → Type
  | false => G₁
  | true => G₂

/-- Each source sort inherits its own additive operations. -/
instance {G₁ G₂ : Type} [AddMonoid G₁] [AddMonoid G₂] (s : Bool) :
    AddMonoid (Group G₁ G₂ s) := by cases s <;> dsimp [Group] <;> infer_instance

/-- Scalar actions are inherited separately at each source sort. -/
instance {F G₁ G₂ : Type} [SMul F G₁] [SMul F G₂] (s : Bool) :
    SMul F (Group G₁ G₂ s) := by cases s <;> dsimp [Group] <;> infer_instance

/-- Lists of received points in the two source groups. -/
@[expose] def groupInputs {G₁ G₂ : Type} (xs : List G₁) (ys : List G₂) :
    Groups (Group G₁ G₂)
  | false => xs
  | true => ys

/-- Uniform sampling, hashing, and signing are selected by ordinary query data. -/
abbrev Query (M : Type) := (ℕ ⊕ M) ⊕ M

/-- Uniform samples are ordinary reply data; hash and signature points are group inputs. -/
@[expose] def Reply {M : Type} : Query M → Type
  | .inl (.inl n) => Fin (n + 1)
  | _ => Unit

/-- The scheme's ordinary oracle family, including the signing oracle. -/
abbrev rawSpec (M G₁ : Type) := (unifSpec + (M →ₒ G₁)) + (M →ₒ G₁)

/-- Supply both generators and the public key as explicit received group inputs. -/
@[expose] def initialInput {G₁ G₂ : Type} (g₁ : G₁) (g₂ : G₂) (pk : G₁ × G₂) :
    Message Unit (Group G₁ G₂) := ⟨(), groupInputs [g₁, pk.1] [g₂, pk.2]⟩

/-- Translate ordinary BLS replies into received group inputs. Requests use only plain data. -/
@[expose] def oracle {M G₁ G₂ : Type} :
    QueryImpl (plainSpec (Group G₁ G₂) (Query M) Reply) (OracleComp (rawSpec M G₁)) := by
  intro ⟨q, _⟩
  rcases q with ((n | m) | m)
  · exact do
      let r ← (rawSpec M G₁).query (.inl (.inl n))
      return ⟨r, groupInputs [] []⟩
  · exact do
      let h ← (rawSpec M G₁).query (.inl (.inr m))
      return ⟨(), groupInputs [h] []⟩
  · exact do
      let s ← (rawSpec M G₁).query (.inr m)
      return ⟨(), groupInputs [s] []⟩

/-- Decode the message and first signature point; an empty signature list denotes zero. -/
@[expose] def forgery {F M G₁ G₂ : Type} [Zero G₁]
    (out : Explained F M (Group G₁ G₂)) : M × G₁ :=
  (out.value.data, (out.value.groups false).headD 0)

end BLS.AGM

namespace BLS

/-- The shared interactive algebraic adversary specialized to BLS. The scheme parameters
index the forgetful map; all generators and public-key points are delivered as group inputs. -/
structure AlgebraicAdversary (F M G₁ G₂ : Type) {Gₜ : Type} [Field F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ]
    (_e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (_g₁ : G₁) (_g₂ : G₂) extends
    GroupModel.Interaction.Adversary F (AGM.Group G₁ G₂) Unit (AGM.Query M) AGM.Reply M where
  /-- All requests are group-free and every final output is exactly one signature point. -/
  protocol : ∀ input, allPathsSatisfy
    (fun q => ∀ s, q.value.groups s = [])
    (fun out => (out.value.groups false).length = 1 ∧ out.value.groups true = [])
    (fun _ => Set.univ) (main input)

/-- Forget the explanations and certificates, forwarding randomness, hashes, and signing
requests to the original scheme oracles and returning the raw decoded forgery. -/
@[expose] def AlgebraicAdversary.toUnforgeableAdversary {F M G₁ G₂ Gₜ : Type}
    [Field F] [SampleableType F] [AddCommGroup G₁] [Module F G₁]
    [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ] [DecidableEq Gₜ]
    {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₁ : G₁} {g₂ : G₂}
    (A : AlgebraicAdversary F M G₁ G₂ e g₁ g₂) :
    SignatureAlg.UnforgeableAdversary (scheme (M := M) e g₁ g₂) where
  main pk := AGM.forgery <$> simulateQ (fun q => AGM.oracle q.value)
    (A.main (AGM.initialInput g₁ g₂ pk))

end BLS
