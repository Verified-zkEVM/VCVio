/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.Security.Target

/-!
# The random-oracle model of SLH-DSA and its security target, checked

`HashSig.SLHDSA.Security.Target` states the model and the target. This file checks that the
statement is not degenerate.

* **The budget constrains.** `replayForger` evaluates `H_msg` once and asks for one signature. It
  is within budget `(1, 1)` (`romQueryBound_replayForger`) and within neither `(0, 1)` nor `(1, 0)`
  (`not_romQueryBound_replayForger`).
* **The adversary's hash queries are counted on every run.** `forgerCount_le_replayForger` applies
  `SignatureAlg.forgerCount_le_of_mem_support_run` to the model: on every run of the counted
  tagged experiment the counter is at most one.
* **The verifier term is a separate term.** At zero budget the right-hand side is exactly
  `(r + 1) · verifyInternalQueryBound / |Y|` (`securityBound_zero`), so the target does not force an
  adversary that makes no query to have advantage zero: the verifier's own queries can still fire.
* **Signing queries enter only through the coverage term.** With no hash query the weighted
  coverage term is the unweighted `targetCoverBound h a k qs`, and the right-hand side is that term
  plus the verifier term at every signing budget (`securityBound_qh_zero`).
* **The target is not vacuous at a real parameter set.** At SLH-DSA-128s, with `qh = qs = 2^64`,
  `|Y| = 2^128`, `c = 2` and `r = 1`, the constants at which the target is proved, the right-hand
  side is below one (`securityBound_128s_lt_one`; crudely about `2^-32`).
* **The verifier count** is `3929` at 128s and `17522` at 256f (`verifyInternalQueryBound_128s`,
  `verifyInternalQueryBound_256f`), the counts of FIPS 205 Algorithm 20 with full chain
  completions.
* **The secrets are oracle answers.** `romScheme_sign_oracle` restates `romScheme_sign` at a
  concrete message: signing queries the `PRF_msg` oracle for the randomizer and draws its secret
  values from `oracleSecret`, the `F` query at the secret-key address applied to `SK.seed`.
* **Neither keyed function of the core is referenced.** The final check walks every `SLHDSA`
  constant the model and the target depend on and finds neither `CorePrimitives.PRF` nor
  `CorePrimitives.PRFmsg`, while it does find the oracle query `PublicHash.f`; the same walk from
  FIPS 205's `keygenInternalM` and `signInternalM`, whose secrets and randomizer are computed by
  `core.PRF` and `core.PRFmsg`, finds both. The walk checks only which constants are referenced; it
  is the equations above that pin where each secret value comes from.
-/

public section

open OracleComp OracleSpec SignatureAlg
open scoped ENNReal

namespace SLHDSA.Security.TargetTest

variable {vp : ValidatedParams} (core : CorePrimitives vp.params)
  [SampleableType core.SkSeed] [SampleableType core.SkPrf] [DecidableEq core.Y]

/-- An adversary that evaluates `H_msg` once and asks for one signature, then returns the empty
message with that signature. -/
def replayForger (e : core.SkSeed ≃ core.Y) (optRand : PublicKeyCore core → ProbComp core.Y)
    (pkSeedDist : ProbComp core.PkSeed) :
    UnforgeableAdversary (romScheme core e optRand pkSeedDist) where
  main pk := do
    let _ ← (liftM (((unifSpec + hashSpec core) +
        (List Byte →ₒ GeneralScheme.SignatureCore vp core)).query
      (.inl (.inr (.inl (.hmsg pk.pkRoot pk.pkSeed pk.pkRoot []))))) :
        OracleComp ((unifSpec + hashSpec core) +
          (List Byte →ₒ GeneralScheme.SignatureCore vp core)) _)
    let s ← (liftM (((unifSpec + hashSpec core) +
        (List Byte →ₒ GeneralScheme.SignatureCore vp core)).query (.inr [])) :
      OracleComp ((unifSpec + hashSpec core) +
        (List Byte →ₒ GeneralScheme.SignatureCore vp core)) _)
    return ([], s)

theorem romQueryBound_replayForger (e : core.SkSeed ≃ core.Y)
    (optRand : PublicKeyCore core → ProbComp core.Y) (pkSeedDist : ProbComp core.PkSeed) :
    (replayForger core e optRand pkSeedDist).RomQueryBound 1 1 := by
  intro pk
  refine ⟨?_, ?_⟩ <;>
    simp [replayForger, isQueryBoundP_query_bind_iff, IsHashQuery, IsSignQuery]

theorem not_romQueryBound_replayForger (e : core.SkSeed ≃ core.Y)
    (optRand : PublicKeyCore core → ProbComp core.Y) (pkSeedDist : ProbComp core.PkSeed)
    (pk : PublicKeyCore core) :
    ¬ (replayForger core e optRand pkSeedDist).RomQueryBound 0 1 ∧
      ¬ (replayForger core e optRand pkSeedDist).RomQueryBound 1 0 := by
  constructor <;> intro h
  · have := (h pk).1
    simp [replayForger, isQueryBoundP_query_bind_iff, IsHashQuery] at this
  · have := (h pk).2
    simp [replayForger, isQueryBoundP_query_bind_iff, IsSignQuery] at this

theorem forgerCount_le_replayForger [SampleableType core.Y] [SampleableType (Bytes vp.params.m)]
    [DecidableEq core.PkSeed] [DecidableEq core.AdrsKey] [DecidableEq core.SkPrf]
    (e : core.SkSeed ≃ core.Y) (optRand : PublicKeyCore core → ProbComp core.Y)
    (pkSeedDist : ProbComp core.PkSeed) {z : Bool × (hashSpec core).QueryCache × ℕ}
    (hz : z ∈ support ((simulateQ (forgerCountingRomImpl (hashSpec core))
      (taggedUnforgeableExperiment (replayForger core e optRand pkSeedDist))).run (∅, 0))) :
    z.2.2 ≤ 1 :=
  forgerCount_le_of_mem_support_run
    (fun pk => (romQueryBound_replayForger core e optRand pkSeedDist pk).1) hz

/-- Signing the empty message queries `PRF_msg` at `(SK.prf, opt_rand, [])` and draws each secret
value as the `F` query at its address applied to `SK.seed`. -/
theorem romScheme_sign_oracle (e : core.SkSeed ≃ core.Y)
    (optRand : PublicKeyCore core → ProbComp core.Y) (pkSeedDist : ProbComp core.PkSeed)
    (pk : PublicKeyCore core) (sk : SecretKeyCore core) :
    (romScheme core e optRand pkSeedDist).sign pk sk [] = (do
      let addrnd ← (optRand pk : ProbComp core.Y)
      let R ← (query (spec := prfMsgSpec core) ⟨sk.skPrf, addrnd, []⟩ :
        OracleComp (unifSpec + hashSpec core) core.Y)
      GeneralScheme.signInternalWithSecretRandomizerM core
        (fun a => PublicHash.f core sk.pkSeed a (e sk.skSeed)) [] sk.pkSeed sk.pkRoot R) :=
  romScheme_sign core e optRand pkSeedDist pk sk []

end SLHDSA.Security.TargetTest

namespace SLHDSA.Security.TargetTest

open KeyedHash.Covering

theorem securityBound_zero (p : Params) (hk : 0 < p.k) (card c r : ℕ) :
    securityBound p card c r 0 0 =
      ((r + 1) * GeneralScheme.verifyInternalQueryBound p : ℕ) * (card : ℝ≥0∞)⁻¹ := by
  simp [securityBound, weightedTargetCoverBound_qw_zero, targetCoverBound_zero p.h p.a p.k hk]

theorem securityBound_qh_zero (p : Params) (card c r qs : ℕ) :
    securityBound p card c r 0 qs =
      targetCoverBound p.h p.a p.k qs +
        ((r + 1) * GeneralScheme.verifyInternalQueryBound p : ℕ) * (card : ℝ≥0∞)⁻¹ := by
  simp [securityBound, weightedTargetCoverBound_qw_zero]

theorem verifyInternalQueryBound_128s :
    GeneralScheme.verifyInternalQueryBound
      (FipsParameterSet.SLHDSA_SHA2_128s.validatedParams).params = 3929 := by
  decide

theorem verifyInternalQueryBound_256f :
    GeneralScheme.verifyInternalQueryBound
      (FipsParameterSet.SLHDSA_SHA2_256f.validatedParams).params = 17522 := by
  decide

/-- Each summand of `targetCoverBound` is at most `qs^r · r^k · 2^(-h r) · 2^(-a k)`. -/
theorem targetCoverBound_le (h a k qs : ℕ) :
    targetCoverBound h a k qs ≤ ∑ r ∈ Finset.range (k + 1),
      ((qs ^ r * r ^ k : ℕ) : ℝ≥0∞) * ((((2 : ℝ≥0∞) ^ h)⁻¹) ^ r * (((2 : ℝ≥0∞) ^ a)⁻¹) ^ k) := by
  refine Finset.sum_le_sum fun r _ => ?_
  gcongr
  · exact Nat.choose_le_pow qs r
  · calc (Finset.univ.filter fun s : Fin k → Fin r => Function.Surjective s).card
          ≤ (Finset.univ : Finset (Fin k → Fin r)).card := Finset.card_filter_le _ _
      _ = r ^ k := by simp

/-- With at most one weighted coverer expected (`qw * w ≤ 1`) and `1 ≤ qs`, each summand of
`weightedTargetCoverBound` is at most `(r + 1) · qs^r · r^k · 2^(-h r) · 2^(-a k)`. -/
theorem weightedTargetCoverBound_le (h a k qs qw : ℕ) (w : ℝ≥0∞) (hqs : 1 ≤ qs)
    (hw : (qw : ℝ≥0∞) * w ≤ 1) :
    weightedTargetCoverBound h a k qs qw w ≤ ∑ r ∈ Finset.range (k + 1),
      (((r + 1) * qs ^ r * r ^ k : ℕ) : ℝ≥0∞) *
        ((((2 : ℝ≥0∞) ^ h)⁻¹) ^ r * (((2 : ℝ≥0∞) ^ a)⁻¹) ^ k) := by
  refine Finset.sum_le_sum fun r _ => ?_
  have hS : (Finset.univ.filter fun s : Fin k → Fin r => Function.Surjective s).card ≤ r ^ k :=
    (Finset.card_filter_le _ _).trans (by simp)
  calc ∑ r₁ ∈ Finset.range (r + 1),
        ((qs.choose (r - r₁) * qw.choose r₁ *
          (Finset.univ.filter fun s : Fin k → Fin r => Function.Surjective s).card : ℕ) :
            ℝ≥0∞) * w ^ r₁ * ((((2 : ℝ≥0∞) ^ h)⁻¹) ^ r * (((2 : ℝ≥0∞) ^ a)⁻¹) ^ k)
      ≤ ∑ _r₁ ∈ Finset.range (r + 1), ((qs ^ r * r ^ k : ℕ) : ℝ≥0∞) *
          ((((2 : ℝ≥0∞) ^ h)⁻¹) ^ r * (((2 : ℝ≥0∞) ^ a)⁻¹) ^ k) := by
        refine Finset.sum_le_sum fun r₁ _ => ?_
        gcongr
        push_cast
        calc (qs.choose (r - r₁) : ℝ≥0∞) * qw.choose r₁ *
              (Finset.univ.filter fun s : Fin k → Fin r => Function.Surjective s).card * w ^ r₁
            = (qs.choose (r - r₁) : ℝ≥0∞) *
                (Finset.univ.filter fun s : Fin k → Fin r => Function.Surjective s).card *
                  ((qw.choose r₁ : ℝ≥0∞) * w ^ r₁) := by ring
          _ ≤ (qs : ℝ≥0∞) ^ r * (r : ℝ≥0∞) ^ k * 1 := by
            gcongr
            · exact_mod_cast (Nat.choose_le_pow qs _).trans
                (Nat.pow_le_pow_right hqs (Nat.sub_le r r₁))
            · exact_mod_cast hS
            · calc (qw.choose r₁ : ℝ≥0∞) * w ^ r₁ ≤ (qw : ℝ≥0∞) ^ r₁ * w ^ r₁ := by
                    gcongr
                    exact_mod_cast Nat.choose_le_pow qw r₁
                _ = ((qw : ℝ≥0∞) * w) ^ r₁ := (mul_pow _ _ _).symm
                _ ≤ 1 := pow_le_one₀ zero_le hw
          _ = (qs : ℝ≥0∞) ^ r * (r : ℝ≥0∞) ^ k := mul_one _
    _ = (((r + 1) * qs ^ r * r ^ k : ℕ) : ℝ≥0∞) *
          ((((2 : ℝ≥0∞) ^ h)⁻¹) ^ r * (((2 : ℝ≥0∞) ^ a)⁻¹) ^ k) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring

theorem term_128s (r : ℕ) :
    (((r + 1) * (2 ^ 64) ^ r * r ^ 14 : ℕ) : ℝ≥0∞) *
        ((((2 : ℝ≥0∞) ^ 63)⁻¹) ^ r * (((2 : ℝ≥0∞) ^ 12)⁻¹) ^ 14)
      = (((r + 1) * 2 ^ r * r ^ 14 : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ 168)⁻¹ := by
  have e : ((r + 1) * (2 ^ 64) ^ r * r ^ 14 : ℕ) = ((r + 1) * 2 ^ r * r ^ 14) * 2 ^ (63 * r) := by
    rw [← pow_mul, show 64 * r = r + 63 * r by ring, pow_add]; ring
  have h2 : (2 : ℝ≥0∞) ^ (63 * r) * ((2 : ℝ≥0∞) ^ 63)⁻¹ ^ r = 1 := by
    rw [← ENNReal.inv_pow, ← pow_mul,
      ENNReal.mul_inv_cancel (by simp) (by simp)]
  have h3 : (((2 : ℝ≥0∞) ^ 12)⁻¹) ^ 14 = ((2 : ℝ≥0∞) ^ 168)⁻¹ := by
    rw [← ENNReal.inv_pow, ← pow_mul]
  rw [e, Nat.cast_mul, h3]
  calc (((r + 1) * 2 ^ r * r ^ 14 : ℕ) : ℝ≥0∞) * ((2 ^ (63 * r) : ℕ) : ℝ≥0∞) *
        (((2 : ℝ≥0∞) ^ 63)⁻¹ ^ r * ((2 : ℝ≥0∞) ^ 168)⁻¹)
      = (((r + 1) * 2 ^ r * r ^ 14 : ℕ) : ℝ≥0∞) *
          ((2 : ℝ≥0∞) ^ (63 * r) * ((2 : ℝ≥0∞) ^ 63)⁻¹ ^ r) * ((2 : ℝ≥0∞) ^ 168)⁻¹ := by
        push_cast; ring
    _ = _ := by rw [h2, mul_one]

theorem securityBound_128s_lt_one :
    securityBound (FipsParameterSet.SLHDSA_SHA2_128s.validatedParams).params (2 ^ 128) 2 1
      (2 ^ 64) (2 ^ 64) < 1 := by
  have hp : (FipsParameterSet.SLHDSA_SHA2_128s.validatedParams).params.h = 63 ∧
      (FipsParameterSet.SLHDSA_SHA2_128s.validatedParams).params.a = 12 ∧
      (FipsParameterSet.SLHDSA_SHA2_128s.validatedParams).params.k = 14 := by decide
  have hV := verifyInternalQueryBound_128s
  rw [securityBound, hp.1, hp.2.1, hp.2.2, hV]
  have hN : (∑ r ∈ Finset.range 15, ((r + 1) * 2 ^ r * r ^ 14 : ℕ)) < 2 ^ 72 := by decide
  have hw : ((2 ^ 64 : ℕ) : ℝ≥0∞) * (((2 ^ 64 : ℕ) : ℝ≥0∞) / ((2 ^ 128 : ℕ) : ℝ≥0∞)) ≤ 1 := by
    rw [← mul_div_assoc, ← Nat.cast_mul, ← pow_add]
    exact (ENNReal.div_self (by simp) (by simp)).le
  have hI : weightedTargetCoverBound 63 12 14 (2 ^ 64) (2 ^ 64)
      (((2 ^ 64 : ℕ) : ℝ≥0∞) / ((2 ^ 128 : ℕ) : ℝ≥0∞)) ≤
        ((2 ^ 72 : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ 168)⁻¹ := by
    refine (weightedTargetCoverBound_le _ _ _ _ _ _ Nat.one_le_two_pow hw).trans ?_
    simp_rw [term_128s, ← Finset.sum_mul, ← Nat.cast_sum]
    gcongr
  have key : ((2 ^ 64 : ℕ) + 1 : ℝ≥0∞) * (((2 ^ 72 : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ 168)⁻¹) +
      ((2 : ℕ) * ((2 ^ 64 : ℕ) : ℝ≥0∞) + (((1 + 1) * 3929 : ℕ) : ℝ≥0∞)) *
        (((2 ^ 128 : ℕ) : ℝ≥0∞))⁻¹ < 1 := by
    rw [← ENNReal.toReal_lt_toReal (by finiteness) ENNReal.one_ne_top]
    rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
    simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_pow,
      ENNReal.toReal_ofNat, ENNReal.toReal_one, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_mul,
      Nat.cast_add, Nat.cast_one]
    norm_num
  refine lt_of_le_of_lt ?_ key
  gcongr

end SLHDSA.Security.TargetTest

/-! ## No secret is computed outside the oracle -/

open Lean Elab Command in
/-- The `SLHDSA` constants reachable from `roots` through the constants each one uses. -/
private meta def reachableSLHDSA (env : Environment) (roots : List Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut stack := roots
  while !stack.isEmpty do
    let c := stack.head!
    stack := stack.tail!
    if seen.contains c then continue
    seen := seen.insert c
    if (`SLHDSA).isPrefixOf c then
      if let some info := env.find? c then
        for d in info.getUsedConstantsAsSet do
          stack := d :: stack
  return seen

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let model := reachableSLHDSA env
    [``SLHDSA.Security.romScheme, ``SLHDSA.Security.SecurityTarget,
      ``SLHDSA.Security.unforgeableAdvantage_romScheme_le]
  if model.contains ``SLHDSA.CorePrimitives.PRF || model.contains ``SLHDSA.CorePrimitives.PRFmsg
  then throwError "the model computes a secret outside the oracle"
  unless model.contains ``SLHDSA.PublicHash.f do
    throwError "the model does not reach the oracle query `PublicHash.f`"
  let control := reachableSLHDSA env
    [``SLHDSA.GeneralScheme.keygenInternalM, ``SLHDSA.GeneralScheme.signInternalM]
  unless control.contains ``SLHDSA.CorePrimitives.PRF &&
      control.contains ``SLHDSA.CorePrimitives.PRFmsg do
    throwError "the control walk does not reach the secret-key fields"
