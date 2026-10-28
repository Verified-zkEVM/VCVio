/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kobi Gurkan, Quang Dao
-/

module
public import VCVio.Schemes.BLS.AGM.Adversary
public import VCVio.CryptoFoundations.HardnessAssumptions.DLog11
import VCVio.CryptoFoundations.GroupModel.LinearFunctional.Interaction
import VCVio.Schemes.BLS.GameIdentification

/-! # The two straight-line BLS algebraic reductions

This follows Gurkan's linear-functional proof of BLS security in the algebraic group model
of Fuchsbauer, Kiltz and Loss (CRYPTO 2018). Both reductions keep a shared lazy scalar cache
and a chronological list of representations of received inputs. Neither enumerates messages.

The good reduction programs hashes as known multiples of the generator and signs using the
first challenge point. The bad reduction chooses its own signing key and programs each hash
as an independently masked affine function of the challenge. The public-key coefficient enters
the good denominator and the bad numerator because BLS supplies a public key in both source groups.
-/

public section

open OracleComp OracleSpec GroupModel.Interaction

namespace BLS

private structure ReductionState (M R V : Type) where
  basis : List V
  cache : (M →ₒ R).QueryCache

private def cached {M R V : Type} [DecidableEq M] [SampleableType R] (m : M) :
    StateT (ReductionState M R V) ProbComp R := fun st => do
  let (r, cache) ← ((M →ₒ R).randomOracle m).run st.cache
  return (r, { st with cache })

private theorem cached_run {M R V : Type} [DecidableEq M] [SampleableType R]
    (m : M) (st : ReductionState M R V) :
    (cached m).run st = (fun z => (z.1, { st with cache := z.2 })) <$>
      ((M →ₒ R).randomOracle m).run st.cache := by
  simp only [cached, StateT.run, bind_pure_comp]

private def reductionOracle {F M G₁ G₂ R V : Type}
    [DecidableEq M] [SampleableType R]
    (hash sign : R → G₁) (hashRep signRep : R → V) :
    QueryImpl (explainedSpec F (AGM.Group G₁ G₂) (AGM.Query M) AGM.Reply)
      (StateT (ReductionState M R V) ProbComp) := by
  intro ⟨⟨q, _⟩, _⟩
  rcases q with ((n | m) | m)
  · exact do
      let r ← liftM (unifSpec.query n : ProbComp _)
      return ⟨r, AGM.groupInputs [] []⟩
  · exact do
      let r ← cached m
      modify fun st => { st with basis := st.basis ++ [hashRep r] }
      return ⟨(), AGM.groupInputs [hash r] []⟩
  · exact do
      let r ← cached m
      modify fun st => { st with basis := st.basis ++ [signRep r] }
      return ⟨(), AGM.groupInputs [sign r] []⟩

private def reductionRun {F M G₁ G₂ R V : Type} [Zero F]
    [AddMonoid G₁] [SMul F G₁] [AddMonoid G₂] [SMul F G₂]
    [DecidableEq M] [SampleableType R]
    (A : GroupModel.Interaction.Adversary F (AGM.Group G₁ G₂) Unit
      (AGM.Query M) AGM.Reply M)
    (g₁ : G₁) (g₂ : G₂) (pk : G₁ × G₂) (hash sign : R → G₁)
    (hashRep signRep : R → V) (basis : List V) :
    ProbComp (Explained F M (AGM.Group G₁ G₂) × List V × R) := do
  let (out, st) ← (simulateQ (reductionOracle hash sign hashRep signRep)
    (A.main (AGM.initialInput g₁ g₂ pk))).run ⟨basis, ∅⟩
  let (target, _) ← (cached out.value.data).run st
  return (out, st.basis, target)

private def coefficients {F M G₁ G₂ : Type}
    (out : Explained F M (AGM.Group G₁ G₂)) : List F :=
  if (out.value.groups false).isEmpty then [] else (out.coefficients false).headD []

/-- Program every hash as `ρ • g₁`, sign with `ρ • X₁`, and divide the represented constant
by the verification gap. The linear coefficient includes the received public-key point. -/
def goodReduction {F M G₁ G₂ Gₜ : Type} [Field F] [SampleableType F]
    [DecidableEq M] [AddCommGroup G₁] [Module F G₁]
    [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ]
    {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₁ : G₁} {g₂ : G₂}
    (A : AlgebraicAdversary F M G₁ G₂ e g₁ g₂) : DLog11.Adversary F G₁ G₂ :=
  fun g X h Y => do
    let (out, basis, target) ← reductionRun A.toAdversary g h (X, Y)
      (fun ρ : F => ρ • g) (fun ρ => ρ • X)
      (fun ρ => (ρ, (0 : F))) (fun ρ => ((0 : F), ρ)) [(1, 0), (0, 1)]
    let repr := evaluate (coefficients out) basis
    return repr.1 / (target - repr.2)

/-- Choose a fresh signing key and program hashes as `a • X₁ + b • g₁`. A zero good-branch
verification gap becomes an affine equation in the challenge scalar; divide its constant
by its slope. Only coefficients on signing replies and the public key enter that equation. -/
def badReduction {F M G₁ G₂ Gₜ : Type} [Field F] [SampleableType F]
    [DecidableEq M] [AddCommGroup G₁] [Module F G₁]
    [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ]
    {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₁ : G₁} {g₂ : G₂}
    (A : AlgebraicAdversary F M G₁ G₂ e g₁ g₂) : DLog11.Adversary F G₁ G₂ :=
  fun g X h _ => do
    let κ ← $ᵗ F
    let point := fun r : F × F => r.1 • X + r.2 • g
    let (out, basis, target) ← reductionRun A.toAdversary g h (κ • g, κ • h)
      point (fun r => κ • point r) (fun _ => ((0 : F), (0 : F))) id [(0, 0), (0, 1)]
    let repr := evaluate (coefficients out) basis
    return (repr.2 - target.2) / (target.1 - repr.1)

end BLS

/-! ## Identifying the standard experiment -/

namespace BLS.AGM

private def withExplainedFinalHash {F M G₁ G₂ Gₜ : Type} [Field F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ]
    {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₁ : G₁} {g₂ : G₂}
    (A : AlgebraicAdversary F M G₁ G₂ e g₁ g₂) (pk : G₁ × G₂) := do
  let out ← A.toAdversary.run oracle (initialInput g₁ g₂ pk)
  let h ← (rawSpec M G₁).query (.inl (.inr out.1.value.data))
  return (out, h)

private theorem withFinalHash_eq_map_explained {F M G₁ G₂ Gₜ : Type}
    [Field F] [SampleableType F] [AddCommGroup G₁] [Module F G₁]
    [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ] [DecidableEq Gₜ]
    {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₁ : G₁} {g₂ : G₂}
    (A : AlgebraicAdversary F M G₁ G₂ e g₁ g₂) (pk : G₁ × G₂) :
    withFinalHash (A.toUnforgeableAdversary.main pk) =
      (fun z => (forgery z.1.1, z.2)) <$> withExplainedFinalHash A pk := by
  have h := A.toAdversary.run_fst oracle (initialInput g₁ g₂ pk)
  simp only [withFinalHash, AlgebraicAdversary.toUnforgeableAdversary]
  rw [← h]
  simp only [withExplainedFinalHash, bind_map_left, map_bind, map_pure]
  rfl

private theorem unforgeableAdvantage_eq_explained {F M G₁ G₂ Gₜ : Type}
    [Field F] [SampleableType F] [AddCommGroup G₁] [Module F G₁] [SampleableType G₁]
    [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ]
    [DecidableEq Gₜ] [DecidableEq M]
    {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₁ : G₁} {g₂ : G₂}
    (A : AlgebraicAdversary F M G₁ G₂ e g₁ g₂)
    (hg₁ : Function.Bijective (· • g₁ : F → G₁)) (he : e g₁ g₂ ≠ 0) :
    SignatureAlg.unforgeableAdvantage (ProbCompRuntime.rom (M →ₒ G₁))
      A.toUnforgeableAdversary =
    Pr{let x ← ($ᵗ F : ProbComp F)
       let z ← (simulateQ (indexedOracle (fun _ => $ᵗ F) (· • g₁)
         (fun ρ => x • (ρ • g₁)) none)
         (withExplainedFinalHash A (x • g₁, x • g₂))).run OracleState.empty}[
      z.1.1.1.value.data ∉ z.2.signed ∧ (forgery z.1.1.1).2 = x • z.1.2] := by
  rw [unforgeableAdvantage_eq_indexed A.toUnforgeableAdversary hg₁ he]
  simp only [withFinalHash_eq_map_explained, simulateQ_map, StateT.run_map,
    prEvent_norm, Winning, forgery]

end BLS.AGM
