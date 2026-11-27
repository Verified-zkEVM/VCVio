/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.ActualWork.Coupling.Guarded
public import HashSig.SLHDSA.Security.PrfKeyBound
import HashSig.SLHDSA.Security.Transport
import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# Probabilities of graph collisions and activated private-key clashes

Encoding aliases for the message key require an admitted signing attempt. The joint hazard bound
uses the public cache and the attempt count on the same run.
-/

public section

open OracleComp OracleSpec SignatureAlg MeasureTheory
open scoped ENNReal
open SLHDSA SLHDSA.Security SLHDSA.SHAKE128s
open SLHDSA.SHAKE128s.Bridge.SharedExperiment.Guarded

namespace SLHDSA.SHAKE128s.Bridge.SharedExperiment.GuardedFill

/-- A message-key encoding alias needs a signing request admitted by the guard. -/
abbrev signingActive (out : Value) : Prop := 1 ≤ out.1.1.2.2.1.2

/-- Secret-seed guesses use the public cache. The message-key charge applies only to an
execution containing an admitted signing attempt. -/
noncomputable def keyCharge (s : FIPS205.core.PkSeed) (out : Value) (C : H.QueryCache) : ℝ≥0∞ :=
  seedCharge FIPS205.core s C + if signingActive out then
    hmsgCharge FIPS205.core C + (Nat.card FIPS205.core.SkPrf : ℝ≥0∞)⁻¹ else 0

/-- The hazard is evaluated after end fill, with the signing count already fixed. -/
def keyHazard (s : FIPS205.core.PkSeed) (out : Value) (secret : Secret)
    (st : LabState FIPS205.core) : Prop :=
  (∃ x, ((slhGraph FIPS205.core s).toSplitCache st).1
    ((secretEncoding FIPS205.core (Equiv.refl _) s).enc secret x) |>.isSome) ∨
  (signingActive out ∧ (HmsgAtPrfKey id secret.2 st.1 ∨ secret.2 = s))

/-- Conditional on the complete retained output and graph, the final uniform draw pays for
both hidden-input guesses and any activated alias. -/
theorem keyHazard_rate (s : FIPS205.core.PkSeed) (out : Value) (st : LabState FIPS205.core) :
    Pr{let secret ← ($ᵗ Secret : ProbComp Secret)}[keyHazard s out secret st] ≤
      keyCharge s out st.1 := by
  have hd : FIPS205.core.KeyDiscipline FIPS205.params :=
    Concrete.keyDiscipline_approvedPrimitives .SLHDSA_SHAKE_128s
  have same (secret : Secret) := exists_isSome_toSplitCache_fst_secretEncoding_enc_iff
    (e := Equiv.refl _) (pkSeed := s) (s := secret) (st := st) hd.keySeparated
  have hidden := prEvent_exists_isSome_apply_secretEncoding_enc_le
    (core := FIPS205.core) (Equiv.refl _) s le_rfl st.1
  have hmsg :=  prEvent_hmsgAtPrfKey_le (core := FIPS205.core) Function.injective_id le_rfl st.1
  have eqKey : Pr{let secret ← ($ᵗ Secret : ProbComp Secret)}[secret.2 = s] =
      (Nat.card FIPS205.core.SkPrf : ℝ≥0∞)⁻¹ := by
    simp only [SampleableType.prEvent_uniformSample_prod, OracleComp.prEvent_bind_const]
    exact SampleableType.prEvent_uniformSample_eq_singleton_natCard (α := FIPS205.core.SkPrf) s
  by_cases active : signingActive out
  · simp only [keyHazard, keyCharge, same, active, true_and, ite_true]
    exact (prEvent_or_le _ _ _).trans (add_le_add hidden
      ((prEvent_or_le _ _ _).trans (add_le_add hmsg eqKey.le)))
  · simpa only [keyHazard, keyCharge, same, active, false_and, or_false, ite_false, add_zero]
      using hidden

/-- A single expectation on the original deferred program funds the graph, hidden-seed and
activated alias hazards on its end fill. No independence is needed within its execution. -/
theorem joint_hazards_le_expected_charge (s : FIPS205.core.PkSeed)
    (adv : Game.Adversary FIPS205.Answer PK)
    (reserve trackRaw : Bool) (caps : Nat × Nat)
    (fallback : (input : LabCommon.Domain) → LabCommon.Range input) :
    let G := slhGraph FIPS205.core s
    let nk := slhNodeKeys FIPS205.core s
    let program := labProgram s adv reserve trackRaw caps fallback
    Pr{let r ← G.deferredFillDraw ($ᵗ Secret) program}[
      (G.Conflict r.2.1 ∨ nk.TCHazard r.2.1) ∨ keyHazard s r.1.1 r.2.2 r.2.1] ≤
      ∫⁻ charge, charge ∂𝒟[(fun r =>
        (2 * ((nk.keyEntries r.2.1.1).encard : ℝ≥0∞) / Nat.card FIPS205.core.Y) +
          keyCharge s r.1 r.2.1.1) <$>
        (simulateQ G.deferredImpl program).run ((∅, ∅), [])] := by
  intro G nk program
  have bound := G.prEvent_deferredFillDraw_add_initial_potential_le_expected_output_charge
    _ _ nk.isCharged (not_or.2 ⟨G.not_conflict_empty, CanonicalGraph.NodeKeys.not_tcHazard_empty⟩)
    (fun C => 2 * ((nk.keyEntries C).encard : ℝ≥0∞) / Nat.card FIPS205.core.Y)
    nk.potential_le_two_mul ($ᵗ Secret) (keyHazard s) (keyCharge s) (keyHazard_rate s) program
  exact le_self_add.trans bound

end SLHDSA.SHAKE128s.Bridge.SharedExperiment.GuardedFill
