/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kobi Gurkan, Quang Dao
-/

module
public import VCVio.Schemes.Schnorr.AGM.Adversary
public import VCVio.CryptoFoundations.GroupModel.LinearFunctional.Affine
public import VCVio.CryptoFoundations.GroupModel.LinearFunctional.Interaction

/-! # Schnorr affine representations

Chronological explanations flatten to the shared `AffineForm`: a constant coefficient of
the generator and a linear coefficient of the public key. A hash explanation must be fixed
before its challenge is drawn. One accepting signature then extracts the secret unless that
challenge cancels the linear coefficient.
-/

public section

open OracleComp GroupModel.Interaction GroupModel.LinearFunctional

namespace Schnorr.AGM

variable {F G : Type}

/-- Interpret a shared affine form as a group element over the generator and public key. -/
@[expose] def evalPoint [Field F] [AddCommGroup G] [Module F G]
    (a : AffineForm F) (g pk : G) : G := a.const • g + a.lin • pk

/-- The simulator's commitment has known coefficients without knowing the secret key. -/
@[expose] def signingRepresentation [Neg F] (c z : F) : AffineForm F := ⟨z, -c⟩

/-- Interpreting a simulated signature gives its programmed commitment. -/
theorem evalPoint_signingRepresentation [Field F] [AddCommGroup G] [Module F G]
    (g pk : G) (c z : F) :
    evalPoint (signingRepresentation c z) g pk = z • g - c • pk := by
  simp [signingRepresentation, evalPoint, sub_eq_add_neg]

/-- Combine affine forms with their outgoing explanation coefficients. -/
@[expose] def combine [Semiring F] (terms : List (F × AffineForm F)) : AffineForm F :=
  ⟨(terms.map fun p => p.1 * p.2.const).sum, (terms.map fun p => p.1 * p.2.lin).sum⟩

/-- Affine combination commutes with interpretation in the group. -/
theorem evalPoint_combine [Field F] [AddCommGroup G] [Module F G]
    (terms : List (F × AffineForm F)) (g pk : G) :
    evalPoint (combine terms) g pk = (terms.map fun p => p.1 • evalPoint p.2 g pk).sum := by
  induction terms with
  | nil => simp [combine, evalPoint]
  | cons p terms ih =>
      simp only [combine, List.map_cons, List.sum_cons, evalPoint] at ih ⊢
      rw [add_smul, add_smul, smul_add, ← mul_smul, ← mul_smul, ← ih]
      abel

/-- The two initial inputs are the generator followed by the public key. -/
@[expose] def initialRepresentations [Zero F] [One F] : List (AffineForm F) :=
  [⟨1, 0⟩, ⟨0, 1⟩]

/-- Interpret the chronological list of received affine representations. -/
@[expose] def representedBasis [Field F] [AddCommGroup G] [Module F G]
    (g pk : G) (reps : List (AffineForm F)) : Groups (Group G) :=
  fun _ => reps.map (fun a => evalPoint a g pk)

/-- The initial representations interpret to the adversary's initial inputs. -/
@[simp] theorem representedBasis_initial [Field F] [AddCommGroup G] [Module F G] (g pk : G) :
    representedBasis g pk (initialRepresentations (F := F)) = (initial g pk).groups := by
  funext s
  simp [representedBasis, initialRepresentations, evalPoint, initial]

/-- Flatten an outgoing vector, using the shared interaction's zero-padding convention. -/
@[expose] def flatten [Semiring F] (coeff : List F) (reps : List (AffineForm F)) : AffineForm F :=
  combine (reps.mapIdx fun n a => ((coeff[n]?).getD 0, a))

/-- Flattening preserves the group element described by the outgoing explanation. -/
theorem evalPoint_flatten [Field F] [AddCommGroup G] [Module F G]
    (g pk : G) (coeff : List F) (reps : List (AffineForm F)) :
    evalPoint (flatten coeff reps) g pk = evaluate coeff (representedBasis g pk reps ()) := by
  rw [flatten, evalPoint_combine]
  simp [representedBasis, evaluate, List.mapIdx_eq_ofFn, List.map_ofFn, Function.comp_def]

/-- A valid singleton group argument has one vector whose flattened form evaluates to it. -/
theorem valid_singleton [Field F] [AddCommGroup G] [Module F G] {D : Type}
    (g pk R : G) (reps : List (AffineForm F)) (out : Explained F D (Group G))
    (hv : out.Valid (representedBasis g pk reps)) (hR : out.value.groups () = [R]) :
    ∃ coeff : List F, out.coefficients () = [coeff] ∧ coeff.length = reps.length ∧
      evalPoint (flatten coeff reps) g pk = R := by
  have h := hv ()
  rw [hR] at h
  cases hc : out.coefficients () with
  | nil => simp [hc] at h
  | cons coeff rest =>
      rw [hc] at h
      cases h with
      | cons hhead htail =>
          cases htail
          exact ⟨coeff, rfl, by simpa [representedBasis] using hhead.1,
            (evalPoint_flatten g pk coeff reps).trans hhead.2⟩

/-- One accepting signature extracts its secret when the first hash explanation's
linear coefficient does not cancel the challenge. -/
theorem extract [Field F] [AddCommGroup G] [Module F G]
    (g : G) (hg : Function.Injective (fun x : F => x • g)) (x c z : F) (a : AffineForm F)
    (hv : z • g = evalPoint a g (x • g) + c • (x • g)) (hne : a.lin + c ≠ 0) :
    (z - a.const) / (a.lin + c) = x := by
  have hz : z = a.const + (a.lin + c) * x := hg (by
    simpa [evalPoint, add_smul, mul_smul, add_assoc] using hv)
  apply (div_eq_iff hne).2
  rw [hz]
  ring

/-- Precisely one challenge cancels a fixed affine coefficient. -/
theorem bad_challenge_iff [Field F] (a : AffineForm F) (c : F) :
    a.lin + c = 0 ↔ c = -a.lin := by
  constructor <;> intro h <;> linear_combination h

/-- A coefficient fixed before a uniform challenge is exceptional with probability `1/|F|`. -/
theorem bad_challenge_probability [Field F] [SampleableType F] [Fintype F]
    (a : AffineForm F) :
    Pr{let c ← $ᵗ F}[a.lin + c = 0] = (Fintype.card F : ENNReal)⁻¹ := by
  simp only [bad_challenge_iff]
  exact SampleableType.prEvent_uniformSample_eq_singleton (-a.lin)

end Schnorr.AGM
