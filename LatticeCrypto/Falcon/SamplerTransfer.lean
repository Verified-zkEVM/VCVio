/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/

module
public import LatticeCrypto.Falcon.Precision
import all LatticeCrypto.Falcon.SamplerMinEntropy
import VCVio.OracleComp.Coercions.SubSpec.Measure

/-!
# Transfer of events from the ideal sampler to `samplerZ`

Under `Primitives.SamplerQuality a ε`, every event on the output of `ffSampling` has mass at most
`((1 + ε)^(4 · 2^κ) · Q)^((a - 1) / a)`, for `Q` its mass with the ideal sampler
(`prob_ffSampling_le_renyi`). Every execution makes `4 · 2^κ` sampler queries
(`pathSum_ffSamplingWith`), each with standard deviation in `[σmin, σmax]`
(`allQueriesSatisfy_ffSamplingWith_leavesIn`), so the Rényi divergence of the two output laws is
at most `(1 + ε)^(4 · 2^κ)`; Rényi probability preservation ([FGdG+25] Lemma 14) gives the event
bound.

## References

- [FGdG+25]: Fouque, Gajland, de Groote, Janneck, Kiltz. "A Closer Look at Falcon."
  ePrint 2024/1769.
-/

public section

open OracleComp OracleSpec LatticeCrypto MeasureTheory
open scoped ENNReal

namespace Falcon

variable {p : Params}

/-- Uniform coins are unconstrained; an ideal sampler query has its standard deviation in
`[σlo, σhi]`. -/
@[expose] def IdealLeafIn (σlo σhi : ℝ) : ℕ ⊕ (ℝ × ℝ) → Prop
  | .inl _ => True
  | .inr q => σlo ≤ q.2 ∧ q.2 ≤ σhi

/-- Weight `1` per ideal sampler query, `0` per uniform coin. -/
@[expose] def samplerCallWeight : ℕ ⊕ (ℝ × ℝ) → ℝ
  | .inl _ => 0
  | .inr _ => 1

/-- Every sampler query of `ffSampling` on a tree with leaves in `[σlo, σhi]` lies in that range. -/
theorem allQueriesSatisfy_ffSamplingWith_leavesIn {σlo σhi : ℝ} :
    ∀ (κ : ℕ) (t : FFTPair κ) (tree : FalconTree κ), tree.LeavesIn σlo σhi →
      AllQueriesSatisfy (ffSamplingWith idealSamplerQuery κ t tree) (IdealLeafIn σlo σhi)
  | 0, (t₀, t₁), .leaf σ, hleaf => by
    have hq : ∀ μ : ℝ, AllQueriesSatisfy (idealSamplerQuery μ σ) (IdealLeafIn σlo σhi) :=
      fun μ => (allQueriesSatisfy_query_iff _ _).2 hleaf
    simp only [ffSamplingWith]
    exact allQueriesSatisfy_bind (hq _) fun _ => allQueriesSatisfy_bind (hq _) fun _ =>
      allQueriesSatisfy_bind (hq _) fun _ => allQueriesSatisfy_bind (hq _) fun _ =>
        allQueriesSatisfy_pure _ _
  | k + 1, (t₀, t₁), .node ℓ left right, hleaf => by
    obtain ⟨hlo, hro⟩ : left.LeavesIn σlo σhi ∧ right.LeavesIn σlo σhi := hleaf
    simp only [ffSamplingWith]
    exact allQueriesSatisfy_bind (allQueriesSatisfy_ffSamplingWith_leavesIn k _ right hro)
      fun _ => allQueriesSatisfy_bind (allQueriesSatisfy_ffSamplingWith_leavesIn k _ left hlo)
        fun _ => allQueriesSatisfy_pure _ _

/-- Every execution of `ffSampling` makes exactly `4 · 2^κ` sampler queries. -/
theorem pathSum_ffSamplingWith :
    ∀ (κ : ℕ) (t : FFTPair κ) (tree : FalconTree κ),
      PathSum samplerCallWeight (ffSamplingWith idealSamplerQuery κ t tree) (4 * 2 ^ κ)
  | 0, (t₀, t₁), .leaf σ => by
    simp only [ffSamplingWith]
    refine .query_bind (Sum.inr _) _ fun _ => .query_bind (Sum.inr _) _ fun _ =>
      .query_bind (Sum.inr _) _ fun _ => .query_bind (Sum.inr _) _ fun _ => .pure _ ?_
    norm_num [samplerCallWeight]
  | k + 1, (t₀, t₁), .node ℓ left right => by
    simp only [ffSamplingWith]
    refine ((pathSum_ffSamplingWith k _ right).bind fun _ =>
      (pathSum_ffSamplingWith k _ left).bind fun _ => PathSum.pure _ le_rfl).weaken
        (le_of_eq ?_)
    ring

instance : ∀ t, Countable ((unifSpec + idealSamplerSpec).Range t)
  | .inl n => inferInstanceAs (Countable (Fin (n + 1)))
  | .inr _ => inferInstanceAs (Countable ℤ)

/-- Uniform coins lifted alongside the ideal sampler keep their law. -/
theorem evalDist_liftComp_unifSpec_idealSamplerSpec {α : Type} [MeasurableSpace α]
    (mx : ProbComp α) : 𝒟[liftComp mx (unifSpec + idealSamplerSpec)] = 𝒟[mx] :=
  evalDist_liftComp_of_evalDistEq (fun n => by
    let : MeasurableSpace (unifSpec.Range n) := ⊤
    have : DiscreteMeasurableSpace (unifSpec.Range n) := ⟨fun _ => trivial⟩
    refine EvalDistEq.of_evalDist_eq ?_
    rw [show (liftM (unifSpec.query n) : OracleComp (unifSpec + idealSamplerSpec) _) =
      unifLift idealSamplerSpec n from rfl, unifLift_eq, evalDist_liftM_query (spec := unifSpec)]
    exact evalDist_liftM_query (spec := unifSpec + idealSamplerSpec) (Sum.inl n)) mx

open InformationTheory in
/-- `SamplerQuality a ε` with `ε ≠ ⊤` forces `σmin > 0`: at `σ' = 0` the reference law
`discreteGaussianMeasure 0 μ` is the zero measure. -/
theorem Primitives.SamplerQuality.sigmaMin_pos {prims : Primitives p} {a : ℝ} {ε : ℝ≥0∞}
    (hq : prims.SamplerQuality a ε) (hε : ε ≠ ⊤) : 0 < p.sigmaMin := by
  by_contra h
  push Not at h
  have hR := hq.renyiDiv_le 0 0 h (by norm_num [Params.sigmaMax])
  have hz : discreteGaussianMeasure 0 0 = 0 := by
    have hs : discreteGaussianSum 0 0 = 0 := by
      simp [discreteGaussianSum, discreteGaussianWeight, tsum_const, Nat.card_eq_zero_of_infinite]
    have h0 : (fun z : ℤ => ENNReal.ofReal (discreteGaussianPMF 0 0 z)) = 0 := funext fun z => by
      simp [discreteGaussianPMF, hs]
    rw [discreteGaussianMeasure, h0, withDensity_zero]
  have hac : ¬ 𝒟[prims.samplerZ 0 0] ≪ (0 : Measure ℤ) := by
    rw [Measure.absolutelyContinuous_zero_iff]
    exact IsProbabilityMeasure.ne_zero _
  rw [hz, renyiDiv_eq_rpow hq.one_lt, renyiMGF_of_not_ac hac,
    ENNReal.top_rpow_of_pos (inv_pos.2 (sub_pos.2 hq.one_lt)), top_le_iff,
    ENNReal.add_eq_top] at hR
  exact hR.elim ENNReal.one_ne_top hε

open InformationTheory in
/-- **Event transfer from the ideal sampler.** Under `SamplerQuality a ε`, every event on the
output of `ffSampling` has mass at most `((1 + ε)^(4 · 2^κ) · Q)^((a - 1) / a)`, for `Q` its
mass under the ideal sampler (Rényi probability preservation over the `4 · 2^κ` queries). -/
theorem prob_ffSampling_le_renyi (prims : Primitives p) {a : ℝ} {ε : ℝ≥0∞}
    (hq : prims.SamplerQuality a ε) (hε : ε ≠ ⊤) (κ : ℕ) (t : FFTPair κ) (tree : FalconTree κ)
    (hl : tree.LeavesIn p.sigmaMin p.sigmaMax) (A : FFTPair κ → Prop) :
    Pr{let z ← prims.ffSampling κ t tree}[A z] ≤
      ((1 + ε) ^ (4 * 2 ^ κ) * Pr{let z ← ffSamplingWith idealSamplerQuery κ t tree}[A z]) ^
        ((a - 1) / a) := by
  classical
  have ha := hq.one_lt
  have hσ0 := hq.sigmaMin_pos hε
  let implQ : QueryImpl (unifSpec + idealSamplerSpec)
      (OracleComp (unifSpec + idealSamplerSpec)) := unifLift idealSamplerSpec +
    (show QueryImpl idealSamplerSpec (OracleComp (unifSpec + idealSamplerSpec)) from
      fun q => liftComp (prims.samplerZ q.1 q.2) (unifSpec + idealSamplerSpec))
  set oa := ffSamplingWith idealSamplerQuery κ t tree
  set ob : OracleComp (unifSpec + idealSamplerSpec) Bool := oa >>= fun z => pure (decide (A z))
  have hsimQ : simulateQ implQ oa =
      liftComp (prims.ffSampling κ t tree) (unifSpec + idealSamplerSpec) := by
    rw [← ffSamplingWith_samplerZ, liftComp_def, simulateQ_ffSamplingWith,
      simulateQ_ffSamplingWith]
    congr 1
    funext μ σ
    rw [simulateQ_idealSamplerQuery]
    rfl
  have hP : Pr{let z ← prims.ffSampling κ t tree}[A z] = 𝒟[simulateQ implQ ob] {true} := by
    rw [prEvent_eq_evalDist_decide, ← evalDist_liftComp_unifSpec_idealSamplerSpec]
    simp only [ob, simulateQ_bind, simulateQ_pure, hsimQ, liftComp_bind, liftComp_pure]
  have hQ : Pr{let z ← oa}[A z] =
      𝒟[simulateQ (QueryImpl.id' (unifSpec + idealSamplerSpec)) ob] {true} := by
    rw [simulateQ_id', prEvent_eq_evalDist_decide]
  have hexpE : Real.exp (Real.log (1 + ε.toReal)) = 1 + ε.toReal :=
    Real.exp_log (by positivity)
  have hE : 0 ≤ Real.log (1 + ε.toReal) :=
    Real.log_nonneg (by linarith [ENNReal.toReal_nonneg (a := ε)])
  generalize Real.log (1 + ε.toReal) = E at hexpE hE
  have hexp1 : ENNReal.ofReal (Real.exp E) = 1 + ε := by
    rw [hexpE, ENNReal.ofReal_add zero_le_one ENNReal.toReal_nonneg, ENNReal.ofReal_one,
      ENNReal.ofReal_toReal hε]
  have hB : ∀ q, IdealLeafIn p.sigmaMin p.sigmaMax q →
      @renyiMGF _ ⊤ a (@evalDist _ _ _ ⊤ (implQ q))
        (@evalDist _ _ _ ⊤ (QueryImpl.id' (unifSpec + idealSamplerSpec) q)) ≤
      ENNReal.ofReal (Real.exp ((a - 1) * E * samplerCallWeight q)) := by
    intro q hV
    rcases q with n | q
    · let : MeasurableSpace (Fin (n + 1)) := ⊤
      have : MeasurableSingletonClass (Fin (n + 1)) := ⟨fun _ => trivial⟩
      have e : QueryImpl.id' (unifSpec + idealSamplerSpec) (Sum.inl n) =
          unifLift idealSamplerSpec n := by
        rw [QueryImpl.id'_apply, unifLift_eq]
      change renyiMGF a 𝒟[unifLift idealSamplerSpec n]
        𝒟[QueryImpl.id' (unifSpec + idealSamplerSpec) (Sum.inl n)] ≤
          ENNReal.ofReal (Real.exp ((a - 1) * E * 0))
      rw [e, mul_zero, Real.exp_zero, ENNReal.ofReal_one]
      exact renyiMGF_self_le ha _ (evalDist_apply_univ_le_one _)
    · obtain ⟨h1, h2⟩ : p.sigmaMin ≤ q.2 ∧ q.2 ≤ p.sigmaMax := hV
      have hq0 : 0 < q.2 := hσ0.trans_le h1
      rw [QueryImpl.id'_apply]
      change @renyiMGF ℤ ⊤ a
          (@evalDist _ _ ℤ ⊤ (liftComp (prims.samplerZ q.1 q.2) (unifSpec + idealSamplerSpec)))
          (@evalDist _ _ ℤ ⊤ (idealSamplerQuery q.1 q.2)) ≤
        ENNReal.ofReal (Real.exp ((a - 1) * E * 1))
      rw [evalDist_liftComp_unifSpec_idealSamplerSpec, evalDist_idealSamplerQuery,
        idealSamplerMeasure_of_pos hq0, mul_one]
      exact renyiMGF_le_of_renyiDiv_le ha ((hq.renyiDiv_le q.1 q.2 h1 h2).trans hexp1.ge)
  have hV : AllQueriesSatisfy ob (IdealLeafIn p.sigmaMin p.sigmaMax) :=
    allQueriesSatisfy_bind (allQueriesSatisfy_ffSamplingWith_leavesIn κ t tree hl) fun _ =>
      allQueriesSatisfy_pure _ _
  have hpath : PathSum samplerCallWeight ob (4 * 2 ^ κ + 0) :=
    (pathSum_ffSamplingWith κ t tree).bind fun _ => PathSum.pure _ le_rfl
  have hM := renyiMGF_simulateQ_le_of_pathSum ha implQ (QueryImpl.id' _)
    (IdealLeafIn p.sigmaMin p.sigmaMax) samplerCallWeight (mul_nonneg (by linarith) hE) hB ob
    hV hpath
  set P := 𝒟[simulateQ implQ ob]
  set Q := 𝒟[simulateQ (QueryImpl.id' (unifSpec + idealSamplerSpec)) ob]
  have hR : renyiDiv a P Q ≤ (1 + ε) ^ (4 * 2 ^ κ) := by
    rw [renyiDiv_eq_rpow ha]
    calc _ ≤ ENNReal.ofReal (Real.exp ((a - 1) * E * (4 * 2 ^ κ + 0))) ^ (a - 1)⁻¹ :=
          ENNReal.rpow_le_rpow hM (inv_nonneg.2 (by linarith))
      _ = _ := by
          have e : (a - 1) * E * (4 * 2 ^ κ + 0) * (a - 1)⁻¹ = ((4 * 2 ^ κ : ℕ) : ℝ) * E := by
            have : a - 1 ≠ 0 := by linarith
            field_simp
            push_cast
            ring
          rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le (inv_nonneg.2 (by linarith)),
            ← Real.exp_mul, e, Real.exp_nat_mul, ENNReal.ofReal_pow (Real.exp_pos _).le,
            hexp1]
  have hRt : renyiDiv a P Q ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.pow_ne_top (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, hε⟩)) hR
  have hpres := measure_rpow_div_renyiDiv_le ha P Q (measurableSet_singleton true)
  have h1 : P {true} ^ (a / (a - 1)) ≤ Q {true} * renyiDiv a P Q :=
    (ENNReal.div_le_iff_le_mul (Or.inr (measure_ne_top _ _)) (Or.inl hRt)).1 hpres
  have hτ : 0 ≤ (a - 1) / a := div_nonneg (by linarith) (by linarith)
  rw [hP, hQ]
  calc P {true} = (P {true} ^ (a / (a - 1))) ^ ((a - 1) / a) := by
        rw [← ENNReal.rpow_mul, show a / (a - 1) * ((a - 1) / a) = 1 by
          have : a - 1 ≠ 0 := by linarith
          have : a ≠ 0 := by linarith
          field_simp, ENNReal.rpow_one]
    _ ≤ (Q {true} * renyiDiv a P Q) ^ ((a - 1) / a) := ENNReal.rpow_le_rpow h1 hτ
    _ ≤ _ := ENNReal.rpow_le_rpow (by rw [mul_comm]; gcongr) hτ

end Falcon

end
