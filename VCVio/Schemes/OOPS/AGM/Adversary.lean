/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.GroupModel.LinearFunctional.SourceGroups
public import VCVio.Schemes.OOPS.Basic
public import VCVio.OracleComp.Traversal

/-! # Certified algebraic OOPS adversaries

An adversary receives the first generator and the second generator/public key. Hash queries
name a topic/degree base; signing queries name a scalar/topic pair. Every query has only plain
data arguments, and every output has exactly one first-source signature point. Forgetting the
explanations forwards exactly these queries to the original signature algorithm's oracles.
-/

public section

open OracleComp OracleSpec GroupModel.Interaction GroupModel.LinearFunctional

namespace OOPS.AGM

/-- Randomness, base hashes, and scalar/topic signing queries. -/
abbrev Query (F T : Type) (degree : ℕ) := (ℕ ⊕ (T × Fin (degree + 1))) ⊕ (F × T)

/-- Uniform samples are plain data; hash and signing replies are source-group inputs. -/
@[expose] def Reply {F T : Type} {degree : ℕ} : Query F T degree → Type
  | .inl (.inl n) => Fin (n + 1)
  | _ => Unit

/-- The signature algorithm's ambient oracles together with its signing interface. -/
abbrev rawSpec (F T G₁ : Type) (degree : ℕ) :=
  (unifSpec + ((T × Fin (degree + 1)) →ₒ G₁)) + ((F × T) →ₒ G₁)

/-- Supply the generators and the second-source public key as received group inputs. -/
@[expose] def initialInput {G₁ G₂ : Type} (g₁ : G₁) (g₂ pk : G₂) :
    Message Unit (SourceGroup G₁ G₂) := ⟨(), sourceInputs [g₁] [g₂, pk]⟩

/-- Forward protocol queries and mark hash/signature points as new received group inputs. -/
@[expose] def oracle {F T G₁ G₂ : Type} {degree : ℕ} :
    QueryImpl (plainSpec (SourceGroup G₁ G₂) (Query F T degree) Reply)
      (OracleComp (rawSpec F T G₁ degree)) := by
  intro ⟨q, _⟩
  rcases q with ((n | i) | mt)
  · exact do
      let r ← (rawSpec F T G₁ degree).query (.inl (.inl n))
      return ⟨r, sourceInputs [] []⟩
  · exact do
      let h ← (rawSpec F T G₁ degree).query (.inl (.inr i))
      return ⟨(), sourceInputs [h] []⟩
  · exact do
      let σ ← (rawSpec F T G₁ degree).query (.inr mt)
      return ⟨(), sourceInputs [σ] []⟩

/-- Decode the scalar/topic message and its first signature point. -/
@[expose] def forgery {F T G₁ G₂ : Type} [Zero G₁]
    (out : Explained F (F × T) (SourceGroup G₁ G₂)) : (F × T) × G₁ :=
  (out.value.data, (out.value.groups false).headD 0)

end OOPS.AGM

namespace OOPS

/-- A shared interactive algebraic adversary with the OOPS query and output protocol.
Generators are supplied as group inputs; the pairing parameters index the forgetful map. -/
structure AlgebraicAdversary (F T G₁ G₂ : Type) {Gₜ : Type} [Field F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ]
    (_e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (_g₁ : G₁) (_g₂ : G₂) (degree : ℕ) extends
    GroupModel.Interaction.Adversary F (SourceGroup G₁ G₂) Unit
      (AGM.Query F T degree) AGM.Reply (F × T) where
  /-- Queries have no group arguments and final outputs contain exactly one signature point. -/
  protocol : ∀ input, allPathsSatisfy
    (fun q => ∀ s, q.value.groups s = [])
    (fun out => (out.value.groups false).length = 1 ∧ out.value.groups true = [])
    (fun _ => Set.univ) (main input)

/-- Forget algebraic certificates while preserving the adversary's exact oracle computation. -/
@[expose] def AlgebraicAdversary.toUnforgeableAdversary {F T G₁ G₂ Gₜ : Type}
    [Field F] [SampleableType F] [AddCommGroup G₁] [Module F G₁]
    [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ] [DecidableEq Gₜ]
    {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₁ : G₁} {g₂ : G₂} {degree : ℕ}
    (A : AlgebraicAdversary F T G₁ G₂ e g₁ g₂ degree) :
    SignatureAlg.UnforgeableAdversary (scheme (T := T) e g₂ degree) where
  main pk := AGM.forgery <$> simulateQ (fun q => AGM.oracle q.value)
    (A.main (AGM.initialInput g₁ g₂ pk))

end OOPS
