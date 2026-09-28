#!/usr/bin/env python3
"""Rewrite Lean sources from VCVio's discrete probability API to its measure-based API.

Usage:
  python3 scripts/migrate-native-probability.py [--dry-run] PATH...

Each PATH is a Lean file or a directory searched recursively for `*.lean`. Files are rewritten
in place unless `--dry-run` is given, in which case a unified diff is printed instead.

Rewrites:
- legacy events: `Pr[= a | mx]` and `Pr[(· = a) | mx]` become `Pr{mx}[= a]`;
  `Pr[fun x => p | mx]` becomes `Pr{x ← mx}[p]`; `Pr[p | mx]` becomes `Pr{x ← mx}[p x]`;
  `Pr[⊥ | mx]` becomes `(1 - Pr{_ ← mx}[True])`;
- `Pr{let x ← e}[…]` items become `Pr{x ← e}[…]`;
- `GameEquiv` becomes `EvalDistEq` and `≡ₚ` becomes `=ᵈ`;
- oracle answer-type binders `[∀ t, MeasurableSpace (spec.Range t)]`,
  `[∀ t, DiscreteMeasurableSpace (spec.Range t)]` and `[∀ t, MeasurableSingletonClass …]` are
  deleted, with the `omit … in` and `variable` lines they leave empty;
- `IsProbabilitySpec` and `IsUniformSpec` binders become `IsMeasureSpec` and
  `IsUniformMeasureSpec`, and `IsUniformSpec.ofFintypeInhabited` becomes
  `IsUniformMeasureSpec.ofFiniteNonempty`;
- renamed declarations (`RENAMES`) and removed modules (`MODULES`).

Everything the script cannot rewrite is reported as `path:line: …` with a pointer into
`docs/agents/probability-migration.md`. The exit status is 0 whether or not anything was
reported; the build is the judge of the result.
"""

from __future__ import annotations

import argparse
import difflib
import re
import sys
from pathlib import Path

GUIDE = "docs/agents/probability-migration.md"

# Declarations renamed between the discrete API and the measure API, keyed by the old name.
# A chain of renames is recorded by its final name.
RENAMES: dict[str, str] = {
    # Probability heads.
    "AdvBound.of_tvDist": "AdvBound.of_measureETVDist",
    "AdvBound.of_gameEquiv": "AdvBound.of_evalDistEq",
    "le_probEvent_iff_triple_indicator": "le_prEvent_iff_triple_indicator",
    "le_probEvent_isSome_contextFork": "le_prEvent_isSome_contextFork",
    "le_probEvent_isSome_seededFork": "le_prEvent_isSome_seededFork",
    "le_probEvent_isSome_seededFork_sq": "le_prEvent_isSome_seededFork_sq",
    "le_probOutput_iff_triple_indicator": "le_prEvent_iff_triple_indicator",
    "le_probOutput_seededFork": "le_prEvent_seededFork",
    "probEvent_adaptivePrefixRunFrom_le": "prEvent_adaptivePrefixRunFrom_le",
    "probEvent_bind_eq_sum_fintype": "prEvent_bind_eq_sum_fintype",
    "probEvent_bind_le_add_bad_disagree": "prEvent_bind_le_add_bad_disagree",
    "probEvent_bind_le_add_bad_of_disagree": "prEvent_bind_le_add_bad_of_disagree",
    "probEvent_bind_le_add_bad_of_disagree'": "prEvent_bind_le_add_bad_of_disagree'",
    "probEvent_bind_le_add_of_disagree": "prEvent_bind_le_add_of_disagree",
    "probEvent_bind_le_probEvent_add": "prEvent_bind_le_prEvent_add",
    "probEvent_cacheCollision_le_birthday": "prEvent_cacheCollision_le_birthday",
    "probEvent_cacheCollision_le_birthday_total": "prEvent_cacheCollision_le_birthday_total",
    "probEvent_cacheCollision_le_birthday_total_tight":
        "prEvent_cacheCollision_le_birthday_total_tight",
    "probEvent_cache_has_value_le": "prEvent_cache_has_value_le",
    "probEvent_cache_has_value_le_of_noCollision": "prEvent_cache_has_value_le_of_noCollision",
    "probEvent_cache_has_value_le_of_unique_preimage":
        "prEvent_cache_has_value_le_of_unique_preimage",
    "probEvent_cache_hits_targets_le_of_noCollision":
        "prEvent_cache_hits_targets_le_of_noCollision",
    "probEvent_cache_hits_targets_le_of_noCollision_homogeneous":
        "prEvent_cache_hits_targets_le_of_noCollision_homogeneous",
    "probEvent_cache_hits_targets_le_of_unique_preimage":
        "prEvent_cache_hits_targets_le_of_unique_preimage",
    "probEvent_cost_gt_le_expectedCost_div": "prEvent_cost_gt_le_expectedCost_div",
    "probEvent_cost_gt_mul_le_expectedCost": "prEvent_cost_gt_mul_le_expectedCost",
    "probEvent_dist_simulateQ_mono": "prEvent_dist_simulateQ_mono",
    "probEvent_eq_one_simulateQ_randomOracle_run_iff":
        "prEvent_eq_one_simulateQ_randomOracle_run_iff",
    "probEvent_eq_one_simulateQ_romImpl_run_iff": "prEvent_eq_one_simulateQ_romImpl_run_iff",
    "probEvent_eq_wp_indicator": "prEvent_eq_wp_indicator",
    "probEvent_eq_wp_propInd": "prEvent_eq_wp_propInd",
    "probEvent_le_of_relTriple": "prEvent_le_of_relTriple",
    "probEvent_le_of_relTriple_simulateQ_run": "prEvent_le_of_relTriple_simulateQ_run",
    "probEvent_logCollision_le_birthday_total": "prEvent_logCollision_le_birthday_total",
    "probEvent_logCollision_le_birthday_total_tight":
        "prEvent_logCollision_le_birthday_total_tight",
    "probEvent_log_entry_eq_le": "prEvent_log_entry_eq_le",
    "probEvent_log_output_heq_le": "prEvent_log_output_heq_le",
    "probEvent_log_output_match_le": "prEvent_log_output_match_le",
    "probEvent_marginal_simulateQ_mono": "prEvent_marginal_simulateQ_mono",
    "probEvent_mem_support": "prEvent_mem_support",
    "probEvent_mono": "prEvent_mono",
    "probEvent_onlineAdaptivePrefixRunFrom_le": "prEvent_onlineAdaptivePrefixRunFrom_le",
    "probEvent_onlineAdaptivePrefixRunFrom_logged_le":
        "prEvent_onlineAdaptivePrefixRunFrom_logged_le",
    "probEvent_pair_collision_le": "prEvent_pair_collision_le",
    "probEvent_stablePhaseRunFrom_exact_le": "prEvent_stablePhaseRunFrom_exact_le",
    "probEvent_stablePhaseRunFrom_le": "prEvent_stablePhaseRunFrom_le",
    "probEvent_stablePhaseRunFrom_logged_le": "prEvent_stablePhaseRunFrom_logged_le",
    "probEvent_val_gt_uniformSample": "prEvent_val_gt_uniformSample",
    "probEvent_withQueryLog_stablePhase_le": "prEvent_withQueryLog_stablePhase_le",
    "probOutput_fresh_cachingOracle_query": "prEvent_fresh_cachingOracle_query",
    "probOutput_generateSeed": "prEvent_generateSeed",
    "probOutput_generateSeed_cons_eq_mul": "prEvent_generateSeed_cons_eq_mul",
    "probOutput_generateSeed_prependValues": "prEvent_generateSeed_prependValues",
    "probOutput_replicate_uniformSample": "prEvent_replicate_uniformSample",
    "probOutput_uniformSample_fun_eval": "prEvent_uniformSample_fun_eval",
    "probOutput_decide_eq_uniformBool_half": "evalDist_decide_eq_uniformBool_half",
    "probOutput_xor_uniform": "evalDist_xor_uniform",
    "probOutput_pair_xor_uniform": "evalDist_pair_xor_uniform",
    "sum_probEvent_option_map_eq_some_le_isSome": "sum_prEvent_option_map_eq_some_le_isSome",
    "triple_probEvent_eq_one": "triple_prEvent_eq_one",
    "triple_probEvent_indicator": "triple_prEvent_indicator",
    "triple_probOutput_eq_one": "triple_prEvent_eq_one",
    "triple_probOutput_indicator": "triple_prEvent_indicator",
    "triple_propInd_iff_le_probEvent": "triple_propInd_iff_le_prEvent",
    "triple_propInd_iff_probEvent_eq_one": "triple_propInd_iff_prEvent_eq_one",
    "tvDist_simulateQ_le_probEvent_bad": "measureETVDist_simulateQ_run'_le_prEvent_bad",
    # Identical-until-bad and per-query slack.
    "tvDist_simulateQ_run_le_probEvent_output_bad": "measureETVDist_simulateQ_run_le_prEvent_bad",
    "tvDist_simulateQ_le_qeps_plus_probEvent_output_bad":
        "measureETVDist_simulateQ_run'_le_queryBoundP_mul_add_prEvent_bad",
    "tvDist_simulateQ_run_le_queryBound_mul_slack_plus_probEvent_bad":
        "measureETVDist_simulateQ_run_le_queryBoundP_mul_add_prEvent_bad",
    "tvDist_simulateQ_le_queryBound_mul_slack_plus_probEvent_bad":
        "measureETVDist_simulateQ_run'_le_queryBoundP_mul_add_prEvent_bad",
    "tvDist_simulateQ_run_le_queryBoundP_mul": "measureETVDist_simulateQ_run_le_queryBoundP_mul",
    "ofReal_tvDist_simulateQ_run_le_expectedQuerySlack_plus_probEvent_output_bad":
        "measureETVDist_simulateQ_run_le_expectedQuerySlack_add_prEvent_bad",
    "ofReal_tvDist_simulateQ_le_expectedQuerySlack_plus_probEvent_output_bad":
        "measureETVDist_simulateQ_run'_le_expectedQuerySlack_add_prEvent_bad",
    "ofReal_tvDist_simulateQ_run_le_queryBound_mul_slack_plus_probEvent_bad":
        "measureETVDist_simulateQ_run_le_queryBoundP_mul_add_prEvent_bad",
    "probEvent_bad_simulateQ_run_le_expectedQuerySlack":
        "prEvent_bad_simulateQ_run_le_expectedQuerySlack",
    "advantage_le_expectedQuerySlack_plus_probEvent_bad":
        "advantage_le_expectedQuerySlack_add_prEvent_bad",
    "advantage_le_expectedQuerySlack_plus_probEvent_bad_of_inv":
        "advantage_le_expectedQuerySlack_add_prEvent_bad_of_inv",
    "advantage_le_expectedQuerySlack_plus_probEvent_bad_of_inv_preserved":
        "advantage_le_expectedQuerySlack_add_prEvent_bad_of_inv_preserved",
    "advantage_le_queryBound_mul_slack_plus_probEvent_bad":
        "advantage_le_queryBound_mul_slack_add_prEvent_bad",
    # Fiat–Shamir and ML-DSA zero knowledge.
    "cmaReal_probEvent_bad_eq_zero": "cmaReal_prEvent_bad_eq_zero",
    "cmaReal_cmaSim_tv_sign_le_cmaSignEpsCore_of_valid":
        "cmaReal_cmaSim_measureETVDist_sign_le_cmaSignEpsCore_of_valid",
    "cmaReal_cmaSim_tv_costly_le_cmaSignEpsCore_of_valid":
        "cmaReal_cmaSim_measureETVDist_costly_le_cmaSignEpsCore_of_valid",
    "hvzkBoundReal": "hvzkBound",
    "evalSPMF_uniform_add_right_swap": "uniform_add_right_swap_evalDistEq",
    "evalSPMF_honest_pregate": "honest_pregate_evalDistEq",
    "evalSPMF_honestExecution_eq_gated": "honestExecution_evalDistEq_gated",
    "hvzkBadMass_eq_probOutput_indicator": "hvzkBadMass_eq_prEvent_indicator",
    # Equality in distribution.
    "GameEquiv.prEvent_eq": "EvalDistEq.prEvent_eq",
    "GameEquiv.rfl": "EvalDistEq.rfl",
    "GameEquiv.symm": "EvalDistEq.symm",
    "GameEquiv.trans": "EvalDistEq.trans",
    "GameEquiv.bind_congr": "EvalDistEq.bind_congr",
    "GameEquiv.map_congr": "EvalDistEq.map_congr",
    "GameEquiv.of_approxRelTriple_zero": "evalDistEq_of_approxRelTriple_zero",
    "GameEquiv.map_uniformSample_bij": "SampleableType.map_uniformSample_evalDistEq_of_bijective",
    "evalDist_eq_of_approxRelTriple_zero": "evalDistEq_of_approxRelTriple_zero",
    "evalDist_eq_of_forall_prEvent_eq": "evalDistEq_of_forall_prEvent_eq_output",
    "evalSPMF_eq_of_relTriple_eqRel": "evalDistEq_of_relTriple_eqRel",
    "evalSPMF_map_eq_of_relTriple": "evalDistEq_map_of_relTriple",
    "evalDist_map_eq_of_relTriple": "evalDistEq_map_of_relTriple",
    "evalSPMF_generateSeed_eq_of_countEq": "evalDistEq_generateSeed_of_countEq",
    "evalDist_generateSeed_eq_of_countEq": "evalDistEq_generateSeed_of_countEq",
    "evalDist_generateSeed_eq_prependValues": "evalDistEq_generateSeed_prependValues",
    "evalDist_liftComp_generateSeed_eq_prependValues":
        "evalDistEq_liftComp_generateSeed_prependValues",
    "evalDist_liftComp_generateSeed_takeAtIndex_run'":
        "evalDistEq_liftComp_generateSeed_takeAtIndex_run'",
    "probOutput_simulateQ_run_eq_of_impl_eq_queryBound":
        "evalDistEq_simulateQ_run_of_impl_eq_queryBound",
    "evalDist_simulateQ_run_eq_of_impl_eq_queryBound":
        "evalDistEq_simulateQ_run_of_impl_eq_queryBound",
    "evalSPMF_step_commute_tape": "evalDistEq_step_commute_tape",
    "evalDist_step_commute_tape": "evalDistEq_step_commute_tape",
    "evalSPMF_uniformSample_vector_succ": "evalDistEq_uniformSample_vector_succ",
    "evalDist_uniformSample_vector_succ": "evalDistEq_uniformSample_vector_succ",
    "relTriple_eqRel_of_evalSPMF_eq": "relTriple_eqRel_of_evalDistEq",
    "relTriple_eqRel_of_probOutput_eq": "relTriple_eqRel_of_evalDistEq",
    "relTriple_eqRel_of_evalDist_eq": "relTriple_eqRel_of_evalDistEq",
    "relTriple_of_evalSPMF_eq": "relTriple_of_evalDistEq",
    "relTriple_of_evalDist_eq": "relTriple_of_evalDistEq",
    "relTriple_of_evalSPMF_eq_left": "relTriple_of_evalDistEq_left",
    "relTriple_of_evalDist_eq_left": "relTriple_of_evalDistEq_left",
    "relTriple_of_evalSPMF_eq_right": "relTriple_of_evalDistEq_right",
    "relTriple_of_evalDist_eq_right": "relTriple_of_evalDistEq_right",
    "relTriple_simulateQ_run'_of_impl_evalSPMF_eq": "relTriple_simulateQ_run'_of_impl_evalDistEq",
    "relTriple_simulateQ_run'_of_impl_evalDist_eq": "relTriple_simulateQ_run'_of_impl_evalDistEq",
    "support_eq_of_evalDist_eq": "support_eq_of_evalDistEq",
    "measureETVDist_simulateQ_run'_le_prEvent_bad_of_evalDist_eq":
        "measureETVDist_simulateQ_run'_le_prEvent_bad_of_evalDistEq",
    "evalSPMF_simulateQ_run_congr": "evalDist_simulateQ_run_congr",
    # Discrete answer measures.
    "evalDist_liftM_query_eq_uniformOn_top": "evalDist_liftM_query_uniform",
    "evalDist_simulateQ_run_congr_of_forall": "evalDist_simulateQ_run_congr",
    "evalDist_liftComp_of_evalDist": "evalDist_liftComp_of_evalDistEq",
    "wp_liftComp_of_evalDist": "wp_liftComp_of_evalDistEq",
    # Classes.
    "IsUniformSpec.ofFintypeInhabited": "IsUniformMeasureSpec.ofFiniteNonempty",
    "GameEquiv": "EvalDistEq",
}

# Declarations whose replacement changes the argument shape; reported, not rewritten.
REPORT_NAMES: dict[str, str] = {
    "prEvent_congr_of_evalDist_eq":
        "use `(EvalDistEq.of_evalDist_eq h).prEvent_eq p`",
    "evalDist_bind_congr_of_evalDist_eq":
        "use `((EvalDistEq.of_evalDist_eq h).bind_left f).evalDist_eq`",
    "evalDist_map_congr_of_evalDist_eq":
        "use `((EvalDistEq.of_evalDist_eq h).map f).evalDist_eq`",
    "evalDist_simulateQ_run_congr":
        "step hypotheses are now `=ᵈ` (see *Query and handler laws*)",
    "evalDist_simulateQ_run'_eq_of_forall":
        "step hypotheses are now `=ᵈ` (see *Query and handler laws*)",
    "MeasureDistEquiv.of_step":
        "step hypotheses are now `=ᵈ` (see *Query and handler laws*)",
    "wp_simulateQ_eq":
        "the per-query hypothesis is now `=ᵈ` (see *Query and handler laws*)",
    "wp_simulateQ_run'_eq":
        "the per-query hypothesis is now `=ᵈ` (see *Query and handler laws*)",
    "evalDist_liftM_query":
        "now gives `(toMeasure t).trim le_top` (see *Query and handler laws*)",
    "prEvent_bind_congr_of_support":
        "now stated for continuations `f g : α → m Prop`; pass `_ _ _ h` and let unification "
        "choose them",
    "prEvent_le_one": "now takes the event computation `mx : m Prop` alone",
    "evalDist_apply_singleton":
        "targets the legacy `Pr[= x | mx]`; `prEvent_eq_evalDist_singleton` relates "
        "`Pr{mx}[= x]` and `𝒟[mx] {x}`",
}

# Modules removed from VCVio, keyed by the old module name.
MODULES: dict[str, list[str]] = {
    "VCVio.OracleComp.QueryTracking.LoggingOracle":
        ["VCVio.OracleComp.QueryTracking.LoggingOracle.Core"],
    "VCVio.OracleComp.QueryTracking.CountingOracle":
        ["VCVio.OracleComp.QueryTracking.CountingOracle.Core"],
    "VCVio.OracleComp.QueryTracking.Tracing": ["VCVio.OracleComp.QueryTracking.Tracing.Core"],
    "VCVio.OracleComp.SimSemantics.QueryImpl.Constructions":
        ["VCVio.OracleComp.SimSemantics.QueryImpl.Constructions.Core"],
    "VCVio.OracleComp.SimSemantics.StateT.Basic":
        ["VCVio.OracleComp.SimSemantics.StateT.Basic.Native"],
    "VCVio.OracleComp.Coercions.Add": ["VCVio.OracleComp.Coercions.Add.Basic"],
    "VCVio.OracleComp.Constructions.Fork": ["VCVio.OracleComp.Constructions.Fork.Basic"],
    "VCVio.CryptoFoundations.ForkMeasure":
        ["VCVio.CryptoFoundations.ReplayFork", "VCVio.CryptoFoundations.SeededFork"],
    "VCVio.CryptoFoundations.SymmEncAlg.MeasureCompatibility":
        ["VCVio.CryptoFoundations.SymmEncAlg"],
    "VCVio.EvalDist.TVDist": ["VCVio.EvalDist.MeasureTVDist.Basic"],
    "VCVio.EvalDist.TVDist.Positivity": ["VCVio.EvalDist.MeasureTVDist.Positivity"],
    "VCVio.EvalDist.MeasureTVDist": ["VCVio.EvalDist.MeasureTVDist.Basic"],
    "VCVio.ProgramLogic.Relational.SimulateQ.Epsilon":
        ["VCVio.ProgramLogic.Relational.SimulateQ.UntilBad"],
    "VCVio.EvalDist.Expectation": ["VCVio.ProgramLogic.Unary.HoareTriple"],
    "VCVio.EvalDist.ExpectationMeasure": ["VCVio.ProgramLogic.Unary.HoareTriple"],
    "VCVio.StateSeparating.DistEquiv": ["VCVio.StateSeparating.MeasureDistEquiv"],
    "VCVio.StateSeparating.Advantage": ["VCVio.StateSeparating.Advantage.Measure"],
    "VCVio.EvalDist.Monad.Disagreement": ["VCVio.EvalDist.Monad.Disagreement.Measure"],
    "VCVio.EvalDist.Instances.FinRatPMF": ["ToMathlib.ProbabilityTheory.FinRatPMF.Measure"],
    "ToMathlib.ProbabilityTheory.FinRatPMF.PMF": ["ToMathlib.ProbabilityTheory.FinRatPMF.Measure"],
    "VCVio.EvalDist.Instances.ReaderT": ["VCVio.EvalDist.MeasureSemantics"],
    "VCVio.EvalDist.Defs.Semantics": ["VCVio.EvalDist.MeasureSemantics"],
    "ToMathlib.ProbabilityTheory.Coupling":
        ["ToMathlib.MeasureTheory.Measure.Coupling",
         "ToMathlib.MeasureTheory.Measure.Coupling.Maximal"],
    "ToMathlib.ProbabilityTheory.OptimalCoupling":
        ["ToMathlib.MeasureTheory.Measure.Coupling",
         "ToMathlib.MeasureTheory.Measure.Coupling.Maximal"],
    "VCVio.ProgramLogic.Relational.Measure.Oracle": ["VCVio.ProgramLogic.Relational.Basic"],
    "VCVio.ProgramLogic.Relational.SimulateQ.Basic":
        ["VCVio.ProgramLogic.Relational.SimulateQ.Coupling",
         "VCVio.ProgramLogic.Relational.SimulateQ.UntilBad"],
    "VCVio.ProgramLogic.Relational.WP.Coherence": ["VCVio.ProgramLogic.Relational.WP.Quantitative"],
    "VCVio.Prelude": ["VCVio.Prelude.Core"],
}

# Native analogues of the most used discrete lemmas, reported where the legacy name appears.
LEGACY_HINTS: dict[str, str] = {
    "probOutput_bind_eq_tsum": "`prEvent_bind_eq_lintegral` (`_of_discrete` for a discrete draw)",
    "probEvent_bind_eq_tsum": "`prEvent_bind_eq_lintegral` (`_of_discrete` for a discrete draw)",
    "probEvent_bind_eq_expectedValue": "`prEvent_bind_eq_lintegral`",
    "probOutput_def": "`prEvent_def`",
    "probEvent_def": "`prEvent_def`",
    "evalSPMF_def": "`𝒟[mx]` is primitive; unfold events with `prEvent_def`",
    "evalSPMF_bind": "`evalDist_bind` or `evalDist_bind_of_discrete`",
    "evalSPMF_map": "`evalDist_map`",
    "evalSPMF_pure": "`evalDist_pure`",
    "evalSPMF_ext": "`EvalDistEq.of_forall_prEvent_eq`, or `Measure.ext` on `𝒟[…]`",
    "evalSPMF_eq_of_evalDist_eq":
        "state the result with `𝒟[…]` or `=ᵈ` (`EvalDistEq.of_evalDist_eq`)",
    "probEvent_eq_eq_probOutput":
        "`Pr{mx}[= x]` is the singleton event; `prEvent_eq_evalDist_singleton`",
    "probEvent_map": "`prEvent_map`",
    "probOutput_map": "`prEvent_map`",
    "probEvent_eq_tsum_ite": "`prEvent_eq_evalDist_of_discrete`, then Mathlib's `Measure` sums",
    "probEvent_eq_tsum_indicator":
        "`prEvent_eq_evalDist_of_discrete`, then Mathlib's `Measure` sums",
    "probOutput_eq_zero_of_not_mem_support": "`prEvent_eq_zero_of_forall_mem_support`",
    "probOutput_eq_zero_iff": "`prEvent_eq_zero_iff`",
    "probEvent_eq_zero_iff": "`prEvent_eq_zero_iff`",
    "probEvent_eq_one_iff":
        "`prEvent_eq_one_iff` (uniform answers) or `prEvent_eq_one_of_forall_mem_support`",
    "probFailure_eq_zero": "nothing on `OracleComp`; `evalDist_apply_univ_eq_one` for total mass",
    "probFailure_def": "`1 - Pr{_ ← mx}[True]`",
    "probOutput_pure": "`prEvent_pure` or `evalDist_pure`",
    "probEvent_pure": "`prEvent_pure`",
    "probOutput_uniformSample":
        "`SampleableType.evalDist_uniformSample` or `prEvent_uniformSample`",
    "probOutput_query": "`evalDist_liftM_query_apply` or `prEvent_query_eq_card_div`",
    "probOutput_le_one": "`prEvent_le_one`",
    "probEvent_le_one": "`prEvent_le_one`",
    "tsum_probOutput_le_one": "`prEvent_le_one` or `measure_univ`",
    "probOutput_ne_top": "`prEvent_ne_top`",
    "probEvent_ne_top": "`prEvent_ne_top`",
    "probOutput_congr": "`prEvent_congr_of_support`",
    "probEvent_congr'": "`prEvent_congr_of_support`",
    "probOutput_bind_congr'": "`prEvent_bind_congr` or `evalDist_bind_congr_of_support`",
    "probEvent_bind_congr'": "`prEvent_bind_congr` or `prEvent_bind_congr_of_support`",
    "probOutput_bind_bind_swap": "`prEvent_bind_bind_swap`",
    "probEvent_bind_bind_swap": "`prEvent_bind_bind_swap`",
    "probOutput_bind_const": "`prEvent_bind_const` or `evalDist_bind_const`",
    "tvDist_le_one": "`measureETVDist_le_one`",
    "tvDist_map_le": "`measureETVDist_map_le`",
    "tvDist_eq_zero_iff": "`measureETVDist_eq_zero_iff`",
    "tvDist_triangle": "`measureETVDist_triangle`",
    "tvDist_self": "`measureETVDist_self`",
    "tvDist_comm": "`measureETVDist_comm`",
    "tvDist_nonneg": "nothing: `measureETVDist` is `ℝ≥0∞`-valued",
}

# Legacy forms left for a person, with the guide section that converts them.
LEGACY_TOKENS: list[tuple[str, str]] = [
    (r"(?<![\w'])evalSPMF(?![\w'])|𝒮\[", "`𝒟[mx]`; see *Notation and definitions*"),
    (r"(?<![\w'.])probOutput(?![\w'])", "`Pr{mx}[= x]` or `𝒟[mx] {x}`"),
    (r"(?<![\w'.])probEvent(?![\w'])", "`Pr{x ← mx}[p x]`"),
    (r"(?<![\w'.])probFailure(?![\w'])", "`1 - Pr{_ ← mx}[True]`"),
    (r"(?<![\w'.])tvDist(?![\w'])", "`measureETVDist`"),
    (r"(?<![\w'.])expectedValue(?![\w'])", "`∫⁻ x, f x ∂𝒟[mx]`"),
    (r"(?<![\w'.])NeverFail(?![\w'])", "nothing on `OracleComp`; see *Classes and binders*"),
    (r"EvalDistCompatible", "operational support lemmas; see *Classes and binders*"),
    (r"PFunctor\.IsProbabilitySpec|PFunctor\.IsUniformSpec",
     "`PFunctor.IsMeasureSpec`; see *Classes and binders*"),
    (r"MeasurableSpace\s*\([^\n]*?\.Range\b",
     "answer measures are discrete; see *Classes and binders*"),
    (r"@(?:OracleSpec\.)?IsUniformMeasureSpec\.ofFiniteNonempty\b",
     "takes the specification and its `Finite` and `Nonempty` instances only"),
    (r"(?<![\w'.])SPMF(?![\w'])", "`Measure`; see *Notation and definitions*"),
    (r"(?<![\w'])[\w'.]*?(?:evalSPMF|probOutput|probEvent|probFailure|tvDist)_[\w'.]*",
     "a legacy lemma name; see *Lemma names*"),
]

OPEN = {"(": ")", "[": "]", "{": "}", "⟨": "⟩"}
CLOSE = {v: k for k, v in OPEN.items()}
IDENT_CHARS = r"[\w'!?₀-₉ₐ-ₜᵢ-ᵪ]"
SIMPLE_BINDER = re.compile(r"_|[^\W\d]" + IDENT_CHARS + r"*")


class Report:
    def __init__(self) -> None:
        self.items: list[tuple[str, int, str]] = []

    def add(self, path: str, text: str, offset: int, message: str) -> None:
        item = (path, text.count("\n", 0, offset) + 1, message)
        if item not in self.items:
            self.items.append(item)


def match_close(s: str, i: int) -> int:
    """Index of the bracket closing the one at `s[i]`, skipping strings and comments."""
    stack = [s[i]]
    j = i + 1
    while j < len(s):
        c = s[j]
        if c == '"':
            j = skip_string(s, j)
            continue
        if s.startswith("--", j):
            nl = s.find("\n", j)
            j = len(s) if nl < 0 else nl
            continue
        if s.startswith("/-", j):
            j = skip_block_comment(s, j)
            continue
        if c in OPEN:
            stack.append(c)
        elif c in CLOSE:
            if stack[-1] != CLOSE[c]:
                raise ValueError(f"mismatched {c!r} at offset {j}")
            stack.pop()
            if not stack:
                return j
        j += 1
    raise ValueError("unclosed bracket")


def skip_string(s: str, j: int) -> int:
    j += 1
    while j < len(s) and s[j] != '"':
        j += 2 if s[j] == "\\" else 1
    return j + 1


def skip_block_comment(s: str, j: int) -> int:
    depth = 0
    while j < len(s):
        if s.startswith("/-", j):
            depth += 1
            j += 2
        elif s.startswith("-/", j):
            depth -= 1
            j += 2
            if depth == 0:
                return j
        else:
            j += 1
    return j


def top_level(s: str, token: str) -> int:
    """Offset of the first occurrence of `token` outside brackets, or -1."""
    depth = 0
    j = 0
    while j < len(s):
        c = s[j]
        if c in OPEN:
            depth += 1
        elif c in CLOSE:
            depth -= 1
        elif depth == 0 and s.startswith(token, j):
            return j
        j += 1
    return -1


def split_top_level(s: str, sep: str) -> list[str]:
    parts: list[str] = []
    depth = 0
    start = 0
    for j, c in enumerate(s):
        if c in OPEN:
            depth += 1
        elif c in CLOSE:
            depth -= 1
        elif c == sep and depth == 0:
            parts.append(s[start:j])
            start = j + 1
    parts.append(s[start:])
    return parts


def strip_parens(term: str) -> str:
    term = term.strip()
    while term.startswith("(") and match_close(term, 0) == len(term) - 1:
        term = term[1:-1].strip()
    return term


def is_atomic(term: str) -> bool:
    term = term.strip()
    if re.fullmatch(r"@?[^\W\d][\w'.!?₀-₉]*", term):
        return True
    return bool(term) and term[0] in OPEN and match_close(term, 0) == len(term) - 1


def fresh_name(*terms: str) -> str:
    used = set(re.findall(r"[^\W\d][\w']*", " ".join(terms)))
    for name in ["x", "y", "z", "w", "v", "u", "a", "b"]:
        if name not in used:
            return name
    n = 0
    while f"x{n}" in used:
        n += 1
    return f"x{n}"


FUN_TYPED_BINDER = (r"fun\s+\(\s*([^\s():]+)\s*:[^()]*(?:\([^()]*\)[^()]*)*\)"
                    r"\s*(?:=>|↦)\s*(.+)")
FUN_BINDER = r"fun\s+(⟨[^⟩]*⟩|[^\s:()]+)(?:\s*:\s*[^=↦]+?)?\s*(?:=>|↦)\s*(.+)"


def convert_legacy_event(event: str, comp: str, prose: bool = False) -> str | None:
    """The native form of `Pr[event | comp]`, or `None` if the event is not understood.

    In a comment (`prose`), only the syntactic event forms are converted: text such as
    `Pr[ |S| ≤ ℓ ]` is mathematics, not a legacy term."""
    event = event.strip()
    comp = comp.strip()
    if not event or not comp:
        return None
    if event == "⊥":
        return f"(1 - Pr{{_ ← {comp}}}[True])"
    m = re.fullmatch(r"=\s*(.+)", event, re.S)
    if m:
        return f"Pr{{{comp}}}[= {m.group(1).strip()}]"
    inner = strip_parens(event)
    m = re.fullmatch(r"·\s*=\s*(.+)", inner, re.S)
    if m and "·" not in m.group(1):
        return f"Pr{{{comp}}}[= {m.group(1).strip()}]"
    m = (re.fullmatch(FUN_TYPED_BINDER, inner, re.S)
         or re.fullmatch(FUN_BINDER, inner, re.S))
    if m:
        binder, body = m.group(1), m.group(2).strip()
        if SIMPLE_BINDER.fullmatch(binder):
            return f"Pr{{{binder} ← {comp}}}[{body}]"
        if binder.startswith("⟨"):
            return f"Pr{{let {binder} ← {comp}}}[{body}]"
        return None
    if "·" in inner:
        # A section `(· op e)` with one hole: substitute a fresh name for the hole.
        if inner.count("·") != 1 or not event.strip().startswith("("):
            return None
        x = fresh_name(inner, comp)
        return f"Pr{{{x} ← {comp}}}[{inner.replace('·', x)}]"
    if prose:
        return None
    x = fresh_name(event, comp)
    pred = event if is_atomic(event) else f"({event})"
    return f"Pr{{{x} ← {comp}}}[{pred} {x}]"


def comment_spans(text: str) -> list[tuple[int, int]]:
    spans: list[tuple[int, int]] = []
    j = 0
    while j < len(text):
        if text[j] == '"':
            j = skip_string(text, j)
        elif text.startswith("--", j):
            end = text.find("\n", j)
            end = len(text) if end < 0 else end
            spans.append((j, end))
            j = end
        elif text.startswith("/-", j):
            end = skip_block_comment(text, j)
            spans.append((j, end))
            j = end
        else:
            j += 1
    return spans


def in_spans(offset: int, spans: list[tuple[int, int]]) -> bool:
    return any(a <= offset < b for a, b in spans)


def rewrite_legacy_events(text: str, report: Report, path: str) -> str:
    spans = comment_spans(text)
    out: list[str] = []
    i = 0
    while True:
        k = text.find("Pr[", i)
        if k < 0:
            out.append(text[i:])
            return "".join(out)
        out.append(text[i:k])
        try:
            close = match_close(text, k + 2)
        except ValueError:
            out.append(text[k:k + 3])
            i = k + 3
            continue
        body = text[k + 3:close]
        bar = top_level(body, "|")
        native = None
        if bar >= 0:
            native = convert_legacy_event(body[:bar], body[bar + 1:], in_spans(k, spans))
        if native is None:
            if not in_spans(k, spans):
                report.add(path, text, k,
                           "legacy event left as is; see *Notation and definitions*")
            out.append(text[k:close + 1])
        else:
            out.append(native)
        i = close + 1


def rewrite_let_items(text: str) -> str:
    out: list[str] = []
    i = 0
    while True:
        k = text.find("Pr{", i)
        if k < 0:
            out.append(text[i:])
            return "".join(out)
        try:
            close = match_close(text, k + 2)
        except ValueError:
            out.append(text[i:k + 3])
            i = k + 3
            continue
        parts = split_top_level(text[k + 3:close], ";")
        # A first item on its own line keeps the name beside the brace and breaks after the
        # arrow, the layout Mathlib's whitespace linter accepts.
        parts[0] = re.sub(r"^\n([ \t]*)let\s+(_|[^\W\d][\w'₀-₉]*)\s*←[ \t]*",
                          r"\2 ←\n\1", parts[0])
        parts = [re.sub(r"^(\s*)let\s+(_|[^\W\d][\w'₀-₉]*)\s*←", r"\1\2 ←", part)
                 for part in parts]
        out.append(text[i:k + 3] + ";".join(parts) + "}")
        i = close + 1


BINDER_FAMILY = re.compile(
    r"\[\s*(?:∀|Π)\s*\(?\s*[^\W\d][\w'₀-₉]*\s*(?::\s*[^,\]]+?)?\)?\s*,\s*"
    r"(?:Discrete)?MeasurableSpace\s*\((?:[^()\[\]]|\([^()]*\))*?\.Range\s+[^()\s]+\s*\)\s*\]"
    r"|\[\s*∀\s*[^\W\d][\w'₀-₉]*\s*(?::\s*[^,\]]+?)?\s*,\s*MeasurableSingletonClass\s*"
    r"\((?:[^()\[\]]|\([^()]*\))*?\.Range\s+[^()\s]+\s*\)\s*\]"
    r"|\[\s*\(\s*[^\W\d][\w'₀-₉]*\s*:\s*[^()]*?\)\s*→\s*(?:Discrete)?MeasurableSpace\s*"
    r"\((?:[^()\[\]]|\([^()]*\))*?\.Range\s+[^()\s]+\s*\)\s*\]"
)


def delete_answer_binders(text: str) -> str:
    lines = text.split("\n")
    out: list[str] = []
    for line in lines:
        new = BINDER_FAMILY.sub("\0", line)
        if new == line:
            out.append(line)
            continue
        new = re.sub(r"[ \t]*\0", "", new)
        stripped = new.strip()
        if stripped in ("", "omit in", "include in"):
            continue
        if re.fullmatch(r"omit\s+in", stripped):
            continue
        out.append(new.rstrip() if new.strip() else new)
    text = "\n".join(out)
    # A `variable` keyword left with no binders on its line or the next.
    text = re.sub(r"(?m)^variable[ \t]*\n(?![ \t]+\S)", "", text)
    return text


CLASS_BINDERS = [
    (re.compile(r"\[\s*(?:OracleSpec\.)?IsProbabilitySpec\s+"), "[OracleSpec.IsMeasureSpec "),
    (re.compile(r"\[\s*(?:OracleSpec\.)?IsUniformSpec\s+"), "[OracleSpec.IsUniformMeasureSpec "),
]


def rewrite_classes(text: str, report: Report, path: str) -> str:
    for regex, replacement in CLASS_BINDERS:
        for m in regex.finditer(text):
            if "Uniform" in replacement:
                report.add(path, text, m.start(),
                           "add `[Fintype (spec.Range t)]` where a cardinality appears")
        text = regex.sub(replacement, text)
    return text


def rename_pattern(name: str) -> re.Pattern[str]:
    return re.compile(r"(?<![\w'!?])" + re.escape(name) + r"(?![\w'!?₀-₉])")


RENAME_PATTERNS = sorted(((rename_pattern(old), new) for old, new in RENAMES.items()),
                         key=lambda p: -len(p[0].pattern))


def rewrite_names(text: str) -> str:
    for pattern, new in RENAME_PATTERNS:
        text = pattern.sub(new, text)
    # `prEvent_le_one` takes the event computation alone.
    text = re.sub(r"(?<![\w'.])prEvent_le_one _ _(?![\w'])", "prEvent_le_one _", text)
    return text.replace("≡ₚ", "=ᵈ")


IMPORT_LINE = re.compile(r"(?m)^((?:public\s+)?(?:meta\s+)?import(?:\s+all)?\s+)(\S+)[ \t]*$")


def rewrite_imports(text: str) -> str:
    """Replace imports of removed modules, skipping a target the file already imports."""
    lines = text.split("\n")
    imported = {m.group(2) for line in lines if (m := IMPORT_LINE.match(line))}
    out: list[str] = []
    for line in lines:
        m = IMPORT_LINE.match(line)
        if not m or m.group(2) not in MODULES:
            out.append(line)
            continue
        for target in MODULES[m.group(2)]:
            if target not in imported:
                imported.add(target)
                out.append(m.group(1) + target)
    return "\n".join(out)


def report_legacy(text: str, report: Report, path: str) -> None:
    spans = comment_spans(text)
    for regex, hint in LEGACY_TOKENS:
        for m in re.finditer(regex, text):
            if not in_spans(m.start(), spans):
                name = m.group(0).rsplit(".", 1)[-1]
                report.add(path, text, m.start(),
                           f"`{m.group(0)}`: {LEGACY_HINTS.get(name, hint)}")
    for name, hint in REPORT_NAMES.items():
        for m in rename_pattern(name).finditer(text):
            if name == "prEvent_le_one" and re.match(r"prEvent_le_one _(?![\w' ]*_)",
                                                     text[m.start():]):
                continue
            if not in_spans(m.start(), spans):
                report.add(path, text, m.start(), f"`{name}`: {hint}")


def migrate(text: str, path: str, report: Report) -> str:
    text = rewrite_imports(text)
    text = rewrite_legacy_events(text, report, path)
    text = rewrite_let_items(text)
    text = delete_answer_binders(text)
    text = rewrite_classes(text, report, path)
    text = rewrite_names(text)
    report_legacy(text, report, path)
    return text


def lean_files(paths: list[str]) -> list[Path]:
    files: list[Path] = []
    for p in map(Path, paths):
        if p.is_dir():
            files.extend(sorted(q for q in p.rglob("*.lean") if ".lake" not in q.parts))
        else:
            files.append(p)
    return files


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("paths", nargs="+")
    parser.add_argument("--dry-run", action="store_true", help="print a diff instead of writing")
    args = parser.parse_args(argv)
    report = Report()
    changed = 0
    for path in lean_files(args.paths):
        old = path.read_text()
        new = migrate(old, str(path), report)
        if new == old:
            continue
        changed += 1
        if args.dry_run:
            sys.stdout.writelines(difflib.unified_diff(
                old.splitlines(keepends=True), new.splitlines(keepends=True),
                str(path), str(path)))
        else:
            path.write_text(new)
    for path, line, message in report.items:
        print(f"{path}:{line}: {message} ({GUIDE})", file=sys.stderr)
    print(f"{changed} file(s) {'would change' if args.dry_run else 'rewritten'}; "
          f"{len(report.items)} site(s) to finish by hand", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
