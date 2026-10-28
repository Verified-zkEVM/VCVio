/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.GroupModel.LinearFunctional.SourceGroups
public import VCVio.Schemes.SynchronizedPS.Basic
public import VCVio.OracleComp.Traversal

/-! # Algebraic adversaries for synchronized PS

The shared algebraic interaction supplies the first generator and the second-source generator
and public-key components. Queries contain only plain data; final output contains one aggregate
point and the target period/message together with certified co-signers. Forgetting explanations
preserves the computation and forwards the same hash and signing requests.
-/

public section

open OracleComp OracleSpec GroupModel.Interaction GroupModel.LinearFunctional

namespace SynchronizedPS.AGM

/-- Randomness, base hashes, and period/scalar signing queries. -/
abbrev Query (F T : Type) := (ℕ ⊕ T) ⊕ (T × F)

/-- Uniform samples are plain data; hash and signing replies are source-group inputs. -/
@[expose] def Reply {F T : Type} : Query F T → Type
  | .inl (.inl n) => Fin (n + 1)
  | _ => Unit

/-- The signature algorithm's ambient oracles together with its signing interface. -/
abbrev rawSpec (F T G₁ : Type) :=
  (unifSpec + (T →ₒ G₁)) + ((T × F) →ₒ G₁)

/-- Supply the generators and the second-source public key as received group inputs. -/
@[expose] def initialInput {G₁ G₂ : Type} (g₁ : G₁) (g₂ : G₂) (pk : G₂ × G₂) :
    Message Unit (SourceGroup G₁ G₂) := ⟨(), sourceInputs [g₁] [g₂, pk.1, pk.2]⟩

/-- Forward protocol queries and mark hash/signature points as new received group inputs. -/
@[expose] def oracle {F T G₁ G₂ : Type} :
    QueryImpl (plainSpec (SourceGroup G₁ G₂) (Query F T) Reply)
      (OracleComp (rawSpec F T G₁)) := by
  intro ⟨q, _⟩
  rcases q with ((n | i) | mt)
  · exact do
      let r ← (rawSpec F T G₁).query (.inl (.inl n))
      return ⟨r, sourceInputs [] []⟩
  · exact do
      let h ← (rawSpec F T G₁).query (.inl (.inr i))
      return ⟨(), sourceInputs [h] []⟩
  · exact do
      let σ ← (rawSpec F T G₁).query (.inr mt)
      return ⟨(), sourceInputs [σ] []⟩

/-- Decode the period/scalar message and its first signature point. -/
@[expose] def forgery {F T G₁ G₂ : Type} [Zero G₁]
    (out : Explained F ((T × F) × List ((F × F) × F)) (SourceGroup G₁ G₂)) :
    AggregateSignatureAlg.Synchronized.Forgery T F (F × F) G₁ :=
  (out.value.data.1, out.value.data.2, (out.value.groups false).headD 0)

end SynchronizedPS.AGM

namespace SynchronizedPS

/-- A shared interactive algebraic adversary with the SynchronizedPS query and output protocol.
Generators are supplied as group inputs; the pairing parameters index the forgetful map. -/
structure AlgebraicAdversary (F T G₁ G₂ : Type) {Gₜ : Type} [Field F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ]
    (_e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (_g₁ : G₁) (_g₂ : G₂) extends
    GroupModel.Interaction.Adversary F (SourceGroup G₁ G₂) Unit
      (AGM.Query F T) AGM.Reply ((T × F) × List ((F × F) × F)) where
  /-- Queries have no group arguments and final outputs contain exactly one signature point. -/
  protocol : ∀ input, allPathsSatisfy
    (fun q => ∀ s, q.value.groups s = [])
    (fun out => (out.value.groups false).length = 1 ∧ out.value.groups true = [])
    (fun _ => Set.univ) (main input)

/-- Forget algebraic certificates while preserving the adversary's exact oracle computation. -/
@[expose] def AlgebraicAdversary.toUnforgeableAdversary {F T G₁ G₂ Gₜ : Type}
    [Field F] [SampleableType F] [AddCommGroup G₁] [Module F G₁]
    [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ] [DecidableEq Gₜ] [DecidableEq T]
    {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₁ : G₁} {g₂ : G₂}
    (A : AlgebraicAdversary F T G₁ G₂ e g₁ g₂) :
    AggregateSignatureAlg.Synchronized.Adversary (scheme (Period := T) e g₂) where
  main pk := AGM.forgery <$> simulateQ (fun q => AGM.oracle q.value)
    (A.main (AGM.initialInput g₁ g₂ pk))

end SynchronizedPS
