#!/usr/bin/env python3
"""Rewrite Lean sources from VCVio's discrete probability API to its measure-based API.

Usage:
  python3 scripts/migrate-native-probability.py [--dry-run] PATH...

Each PATH is a Lean file or a directory searched recursively for `*.lean`. Files are rewritten
in place unless `--dry-run` is given, in which case a unified diff is printed instead.

Rewrites:
- legacy events: `Pr[= a | mx]` and `Pr[(· = a) | mx]` become `Pr{let x ← mx}[x = a]`;
  `Pr[fun x => p | mx]` becomes `Pr{let x ← mx}[p]`; `Pr[p | mx]` becomes `Pr{let x ← mx}[p x]`;
  `Pr[⊥ | mx]` becomes `prFail mx`;
- singleton events `Pr{mx}[= a]` of earlier versions become `Pr{let x ← mx}[x = a]`;
- bare draws `Pr{x ← e}[…]` become the `do` statements `Pr{let x ← e}[…]`, parenthesizing a
  right-hand side that spans several lines;
- `GameEquiv` becomes `EvalDistEq` and `≡ₚ` becomes `=ᵈ`, and an equation of output
  distributions `𝒮[A] = 𝒮[B]` becomes `A =ᵈ B`, parenthesizing a side that is not an
  application;
- oracle answer-type binders `[∀ t, MeasurableSpace (spec.Range t)]`,
  `[∀ t, DiscreteMeasurableSpace (spec.Range t)]` and `[∀ t, MeasurableSingletonClass …]` are
  deleted, with the `omit … in` and `variable` lines they leave empty;
- `IsProbabilitySpec` and `IsUniformSpec` binders become `AnswerMeasure` and
  `UniformAnswerMeasure`, and `IsUniformSpec.ofFintypeInhabited` becomes
  `UniformAnswerMeasure.ofFiniteNonempty`;
- renamed declarations (`RENAMES`) and removed modules (`MODULES`).

Everything the script cannot rewrite is reported as `path:line: …` with a pointer into
`docs/agents/probability-migration.md`. A name in the discrete API's style (`probOutput_…`,
`evalSPMF_…`) that one of the given files declares is the project's own and is not reported at its
uses; a declaration of such a name that VCVio has a replacement for is reported once, where it is
declared. The exit status is 0 whether or not anything was reported; the build is the judge of the
result.
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
    # Answer measures and the reading scopes.
    "IsUniformMeasureSpec": "UniformAnswerMeasure",
    "IsMeasureSpec": "AnswerMeasure",
    "OracleComp.Qualitative": "OracleComp.Necessary",
    "OracleComp.Angelic": "OracleComp.Possible",
    "OracleComp.Quantitative": "OracleComp.Lower",
    "ExpectationWP.Quantitative": "ExpectationWP.Lower",
    # The expectation interpretation and its laws.
    "MeasureProgramLogic.measureWP": "ExpectationWP.wpMonad",
    "MeasureProgramLogic.toMAlgOrdered": "ExpectationWP.algebra",
    "MeasureProgramLogic": "ExpectationWP",
    # The same scopes written relative to an opened `OracleComp`.
    "Qualitative.Spec": "Necessary.Spec",
    "Qualitative.prEvent_eq_one_iff_triple": "Necessary.prEvent_eq_one_iff_triple",
    "Angelic.Spec": "Possible.Spec",
    "Quantitative.Spec": "Lower.Spec",
    "exp_norm": "expect_arith",
    "game_rule": "expect_norm, expect_eval",
    # Probability heads.
    "AdvBound.of_tvDist": "AdvBound.of_etvDist",
    "AdvBound.of_measureETVDist": "AdvBound.of_etvDist",
    "AdvBound.of_gameEquiv": "AdvBound.of_evalDistEq",
    "wpProp_iff_probEvent_eq_one": "OracleComp.Necessary.prEvent_eq_one_iff_triple",
    # Failure probability.
    "probFailure": "prFail",
    "probFailure_le_one": "prFail_le_one",
    "probFailure_ne_top": "prFail_ne_top",
    "probFailure_pure": "prFail_pure",
    "probFailure_failure": "prFail_failure",
    "probFailure_map": "prFail_map",
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
    # Root-level lemmas of the discrete API whose counterparts are stated for oracle computations
    # or uniform draws, in those namespaces; same arguments.
    "tsum_probOutput_bind_mul": "OracleComp.tsum_prEvent_bind_mul",
    "tsum_probOutput_pure_mul": "OracleComp.tsum_prEvent_pure_mul",
    "tsum_probOutput_map_mul": "OracleComp.tsum_prEvent_map_mul",
    "probOutput_ne_zero_of_mem_support": "OracleComp.prEvent_ne_zero_of_mem_support",
    "probEvent_uniformSample": "SampleableType.prEvent_uniformSample",
    "probEvent_or_le": "prEvent_or_le",
    "probEvent_le_of_eq_bind_hiddenReadList": "prEvent_le_of_eq_bind_hiddenReadList",
    "probEvent_bind_fire_le_of_gen": "prEvent_bind_fire_le_of_gen",
    "SPMFSemantics.withStateOracle": "MeasureSemanticsVia.withStateOracle",
    "triple_probEvent_eq_one": "triple_prEvent_eq_one",
    "triple_probEvent_indicator": "triple_prEvent_indicator",
    "triple_probOutput_eq_one": "triple_prEvent_eq_one",
    "triple_probOutput_indicator": "triple_prEvent_indicator",
    "triple_propInd_iff_le_probEvent": "triple_propInd_iff_le_prEvent",
    "triple_propInd_iff_probEvent_eq_one": "triple_propInd_iff_prEvent_eq_one",
    "tvDist_simulateQ_le_probEvent_bad": "etvDist_simulateQ_run'_le_prEvent_bad",
    # Identical-until-bad and per-query slack.
    "tvDist_simulateQ_run_le_probEvent_output_bad": "etvDist_simulateQ_run_le_prEvent_bad",
    "tvDist_simulateQ_le_qeps_plus_probEvent_output_bad":
        "etvDist_simulateQ_run'_le_queryBoundP_mul_add_prEvent_bad",
    "tvDist_simulateQ_run_le_queryBound_mul_slack_plus_probEvent_bad":
        "etvDist_simulateQ_run_le_queryBoundP_mul_add_prEvent_bad",
    "tvDist_simulateQ_le_queryBound_mul_slack_plus_probEvent_bad":
        "etvDist_simulateQ_run'_le_queryBoundP_mul_add_prEvent_bad",
    "tvDist_simulateQ_run_le_queryBoundP_mul": "etvDist_simulateQ_run_le_queryBoundP_mul",
    "ofReal_tvDist_simulateQ_run_le_expectedQuerySlack_plus_probEvent_output_bad":
        "etvDist_simulateQ_run_le_expectedQuerySlack_add_prEvent_bad",
    "ofReal_tvDist_simulateQ_le_expectedQuerySlack_plus_probEvent_output_bad":
        "etvDist_simulateQ_run'_le_expectedQuerySlack_add_prEvent_bad",
    "ofReal_tvDist_simulateQ_run_le_queryBound_mul_slack_plus_probEvent_bad":
        "etvDist_simulateQ_run_le_queryBoundP_mul_add_prEvent_bad",
    # The same bounds stated on the measure-level distance of a chosen σ-algebra.
    "measureETVDist_simulateQ_run_le_prEvent_bad": "etvDist_simulateQ_run_le_prEvent_bad",
    "measureETVDist_simulateQ_run'_le_prEvent_bad": "etvDist_simulateQ_run'_le_prEvent_bad",
    "measureETVDist_simulateQ_run'_le_prEvent_bad_of_run_eq":
        "etvDist_simulateQ_run'_le_prEvent_bad_of_run_eq",
    "measureETVDist_simulateQ_run'_le_prEvent_bad_of_evalDistEq":
        "etvDist_simulateQ_run'_le_prEvent_bad_of_evalDistEq",
    "measureETVDist_simulateQ_run_le_queryBoundP_mul_add_prEvent_bad":
        "etvDist_simulateQ_run_le_queryBoundP_mul_add_prEvent_bad",
    "measureETVDist_simulateQ_run'_le_queryBoundP_mul_add_prEvent_bad":
        "etvDist_simulateQ_run'_le_queryBoundP_mul_add_prEvent_bad",
    "measureETVDist_simulateQ_run_le_queryBoundP_mul": "etvDist_simulateQ_run_le_queryBoundP_mul",
    "measureETVDist_simulateQ_run_le_expectedQuerySlack_add_prEvent_bad":
        "etvDist_simulateQ_run_le_expectedQuerySlack_add_prEvent_bad",
    "measureETVDist_simulateQ_run'_le_expectedQuerySlack_add_prEvent_bad":
        "etvDist_simulateQ_run'_le_expectedQuerySlack_add_prEvent_bad",
    "measureETVDist_withProgramming_withCachingTrackingPolicy_run_le_prEvent_bad":
        "etvDist_withProgramming_withCachingTrackingPolicy_run_le_prEvent_bad",
    "measureETVDist_simulateQ_withCaching_withProgramming_le_prEvent_bad":
        "etvDist_simulateQ_withCaching_withProgramming_le_prEvent_bad",
    "measureETVDist_simulateQ_randomOracle_withProgramming_le_prEvent_bad":
        "etvDist_simulateQ_randomOracle_withProgramming_le_prEvent_bad",
    "measureETVDist_bind_left_le_tsum": "etvDist_bind_left_le_tsum",
    "lintegral_simulateQ_run_eq_of_rel": "wp_simulateQ_run_eq_of_rel",
    "advantage_le_measureETVDist": "advantage_le_etvDist",
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
    # Coinductive responders.
    "ofStateQueryImpl": "ofQueryImpl",
    "ofStateQueryImpl_state": "ofQueryImpl_state",
    "answerSPMF": "answerComp",
    "answerSPMF_ofSPMF": "answerComp_ofQueryImpl",
    "answerKernel_eq_toMeasure": "answerKernel_eq_evalDist",
    "stepAgainstKernel_eq_toMeasure": "stepAgainstKernel_eq_evalDist",
    "iterateAgainstKernel_eq_toMeasure": "iterateAgainstKernel_eq_evalDist",
    "probOutput_none_runWithInput": "prEvent_none_runWithInput",
    # Fiat–Shamir and ML-DSA zero knowledge.
    "cmaReal_probEvent_bad_eq_zero": "cmaReal_prEvent_bad_eq_zero",
    "cmaReal_cmaSim_tv_sign_le_cmaSignEpsCore_of_valid":
        "cmaReal_cmaSim_etvDist_sign_le_cmaSignEpsCore_of_valid",
    "cmaReal_cmaSim_tv_costly_le_cmaSignEpsCore_of_valid":
        "cmaReal_cmaSim_etvDist_costly_le_cmaSignEpsCore_of_valid",
    "cmaReal_cmaSim_measureETVDist_sign_le_cmaSignEpsCore_of_valid":
        "cmaReal_cmaSim_etvDist_sign_le_cmaSignEpsCore_of_valid",
    "cmaReal_cmaSim_measureETVDist_costly_le_cmaSignEpsCore_of_valid":
        "cmaReal_cmaSim_etvDist_costly_le_cmaSignEpsCore_of_valid",
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
        "etvDist_simulateQ_run'_le_prEvent_bad_of_evalDistEq",
    "evalSPMF_simulateQ_run_congr": "evalDist_simulateQ_run_congr",
    # Discrete answer measures.
    "evalDist_liftM_query_eq_uniformOn_top": "evalDist_liftM_query_uniform",
    "evalDist_simulateQ_run_congr_of_forall": "evalDist_simulateQ_run_congr",
    "evalDist_liftComp_of_evalDist": "evalDist_liftComp_of_evalDistEq",
    "wp_liftComp_of_evalDist": "wp_liftComp_of_evalDistEq",
    # Classes.
    "IsUniformSpec.ofFintypeInhabited": "UniformAnswerMeasure.ofFiniteNonempty",
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
    "prEvent_le_one": "now takes the event computation `mx : m Prop` alone",
    "evalDist_apply_singleton":
        "targets the removed `Pr[= x | mx]`; `prEvent_eq_evalDist_singleton` relates "
        "`Pr{let y ← mx}[y = x]` and `𝒟[mx] {x}`",
    "evalDist_apply_setOf":
        "targets the removed `Pr[p | mx]`; `prEvent_eq_evalDist_of_discrete` relates "
        "`Pr{let x ← mx}[p x]` and `𝒟[mx] {x | p x}`",
    "evalDist_apply_univ":
        "targets the removed `Pr[⊥ | mx]`; `prFail_eq_one_sub_evalDist_univ` relates "
        "`prFail mx` and `𝒟[mx] Set.univ`",
}

# Modules removed from VCVio, keyed by the old module name.
MODULES: dict[str, list[str]] = {
    "VCVio.ProgramLogic.Unary.WP.Qualitative": ["VCVio.ProgramLogic.Unary.WP.Necessary"],
    "VCVio.ProgramLogic.Unary.WP.QualitativeSpecs":
        ["VCVio.ProgramLogic.Unary.WP.NecessarySpecs"],
    "VCVio.ProgramLogic.Unary.WP.Angelic": ["VCVio.ProgramLogic.Unary.WP.Possible"],
    "VCVio.ProgramLogic.Unary.WP.Quantitative": ["VCVio.ProgramLogic.Unary.WP.Lower"],
    "VCVio.ProgramLogic.Unary.WP.QuantitativeSpecs": ["VCVio.ProgramLogic.Unary.WP.LowerSpecs"],
    "VCVio.EvalDist.ProbabilityNotation.Attr": ["VCVio.Prelude.Core"],
    "VCVio.OracleComp.QueryTracking.LoggingOracle":
        ["VCVio.OracleComp.QueryTracking.LoggingOracle.Core"],
    "VCVio.OracleComp.QueryTracking.CountingOracle":
        ["VCVio.OracleComp.QueryTracking.CountingOracle.Core"],
    "VCVio.OracleComp.QueryTracking.Tracing": ["VCVio.OracleComp.QueryTracking.Tracing.Core"],
    "VCVio.OracleComp.SimSemantics.QueryImpl.Constructions":
        ["VCVio.OracleComp.SimSemantics.QueryImpl.Constructions.Core"],
    "VCVio.OracleComp.SimSemantics.StateT.Basic.Native":
        ["VCVio.OracleComp.SimSemantics.StateT.Basic"],
    "VCVio.OracleComp.Coercions.Add": ["VCVio.OracleComp.Coercions.Add.Basic"],
    "VCVio.OracleComp.Constructions.Fork": ["VCVio.OracleComp.Constructions.Fork.Basic"],
    "VCVio.CryptoFoundations.ForkMeasure":
        ["VCVio.CryptoFoundations.ReplayFork", "VCVio.CryptoFoundations.SeededFork"],
    "VCVio.CryptoFoundations.SymmEncAlg.MeasureCompatibility":
        ["VCVio.CryptoFoundations.SymmEncAlg"],
    "VCVio.EvalDist.TVDist": ["VCVio.EvalDist.EvalDistTV"],
    "VCVio.EvalDist.TVDist.Positivity": ["VCVio.EvalDist.MeasureTVDist.Positivity"],
    "VCVio.EvalDist.MeasureTVDist": ["VCVio.EvalDist.MeasureTVDist.Basic"],
    "VCVio.ProgramLogic.Relational.SimulateQ.Epsilon":
        ["VCVio.ProgramLogic.Relational.SimulateQ.UntilBad"],
    "VCVio.EvalDist.ExpectationMeasure": ["VCVio.ProgramLogic.Unary.HoareTriple"],
    "VCVio.EvalDist.RenyiDivergence": ["ToMathlib.Probability.Divergence.Renyi"],
    "ToMathlib.Probability.ProbabilityMassFunction.RenyiDivergence":
        ["ToMathlib.Probability.Divergence.Renyi"],
    "ToMathlib.Probability.Divergence.RenyiDiscrete":
        ["ToMathlib.Probability.Divergence.RenyiTotalVariation"],
    "ToMathlib.Probability.ProbabilityMassFunction.RadonNikodym":
        ["ToMathlib.Probability.Divergence.Renyi"],
    "ToMathlib.Probability.ProbabilityMassFunction.TotalVariation":
        ["ToMathlib.MeasureTheory.Measure.TotalVariation"],
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
    # The discrete layer itself.
    "ToMathlib.ProbabilityTheory.SPMF": [],
    "ToMathlib.Probability.ProbabilityMassFunction.Lemmas":
        ["Mathlib.Probability.Distributions.Uniform"],
    "ToMathlib.Probability.ProbabilityMassFunction.Measure": [],
    "VCVio.EvalDist.Defs.Basic":
        ["VCVio.EvalDist.Defs.Measure", "VCVio.EvalDist.ProbabilityNotation"],
    "VCVio.EvalDist.Defs.AlternativeMonad":
        ["VCVio.EvalDist.Defs.Support.Failure", "VCVio.EvalDist.ProbabilityNotation"],
    "VCVio.EvalDist.Defs.NeverFails":
        ["VCVio.EvalDist.Defs.Support.Failure", "VCVio.EvalDist.Monad.Seq"],
    "VCVio.EvalDist.FailureMeasure": ["VCVio.EvalDist.Defs.Measure", "VCVio.EvalDist.WithFailure"],
    "VCVio.EvalDist.Bool": ["VCVio.EvalDist.Monad.Map"],
    "VCVio.EvalDist.BitVec": ["VCVio.EvalDist.Monad.Map"],
    "VCVio.EvalDist.Option": ["VCVio.EvalDist.Monad.Map"],
    "VCVio.EvalDist.Fintype": ["VCVio.EvalDist.Monad.Basic"],
    "VCVio.EvalDist.PFunctor": ["VCVio.EvalDist.PFunctorSupport"],
    "VCVio.EvalDist.PFunctorMeasure": ["VCVio.EvalDist.PFunctorMeasure.Core"],
    "VCVio.OracleComp.EvalDist.UniformCompatibility":
        ["VCVio.OracleComp.EvalDist.Measure", "VCVio.OracleComp.EvalDist.MeasureSpec"],
    "VCVio.OracleComp.Constructions.SampleableType.MeasureCompatibility":
        ["VCVio.OracleComp.Constructions.SampleableType.Measure"],
    "VCVio.OracleComp.Constructions.SampleableType.NativeMeasure":
        ["VCVio.OracleComp.Constructions.SampleableType.Measure"],
    "VCVio.Native": ["VCVio.Foundations"],
    "VCVio.OracleComp.SimSemantics.WriterT.Basic": ["VCVio.OracleComp.SimSemantics.WriterT.Core"],
}

# Native analogues of the most used discrete lemmas, reported where the legacy name appears.
LEGACY_HINTS: dict[str, str] = {
    "probOutput_bind_eq_tsum":
        "`OracleComp.prEvent_bind_eq_tsum`, or `prEvent_bind_eq_lintegral` in another monad",
    "probEvent_bind_eq_tsum":
        "`OracleComp.prEvent_bind_eq_tsum`, or `prEvent_bind_eq_lintegral` in another monad",
    "tsum_probOutput_eq_one": "`OracleComp.tsum_prEvent_eq_one`",
    "tsum_probOutput_eq_one'": "`OracleComp.tsum_prEvent_eq_one`",
    "tsum_probOutput_le_one": "`OracleComp.tsum_prEvent_le_one`",
    "probEvent_bind_eq_expectedValue": "`prEvent_bind_eq_lintegral`",
    "probOutput_def": "`prEvent_eq_evalDist_singleton` (an output's probability is its singleton's "
                      "measure)",
    "probEvent_def": "`prEvent_eq_evalDist_of_discrete`, or `prEvent_eq_evalDist_map` on the output "
                     "measure",
    "evalSPMF_def": "`𝒟[mx]` is primitive; an event is an expectation, and "
                    "`prEvent_eq_evalDist_of_discrete` reaches the measure",
    "prEvent_bind_congr_of_support":
        "`prEvent_bind_congr` when the continuations' events agree at every `x`, or "
        "`wp_congr_of_support` on the `expect_norm` normal form when they agree on "
        "`support mx`",
    "evalSPMF_bind": "`evalDist_bind` or `evalDist_bind_of_discrete`",
    "evalSPMF_map": "`evalDist_map`",
    "evalSPMF_pure": "`evalDist_pure`",
    "evalSPMF_ext": "`EvalDistEq.of_forall_prEvent_eq`, or `Measure.ext` on `𝒟[…]`",
    "evalSPMF_eq_of_evalDist_eq":
        "state the result with `𝒟[…]` or `=ᵈ` (`EvalDistEq.of_evalDist_eq`)",
    "probEvent_eq_eq_probOutput":
        "`Pr{let y ← mx}[y = x]` is the singleton event; `prEvent_eq_evalDist_singleton`",
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
    "probFailure_eq_zero": "`OracleComp.prFail_eq_zero`, or `prFail_eq_zero_iff` in another monad",
    "probFailure_def": "`prFail_def`",
    "probFailure_bind_eq_add_tsum": "`prFail_bind_eq_add_lintegral_of_discrete`",
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
    "probEvent_bind_congr'": "`prEvent_bind_congr`, or `wp_congr_of_support` on the `expect_norm` "
                             "normal form",
    "probOutput_bind_bind_swap": "`prEvent_bind_bind_swap`",
    "probEvent_bind_bind_swap": "`prEvent_bind_bind_swap`",
    "probOutput_bind_const": "`evalDist_bind_const` (`OracleComp.evalDist_bind_const` for a "
                             "lossless oracle computation); for an event, "
                             "`simp only [expect_norm, wp_const]`",
    "evalSPMF_bind_congr": "`evalDist_bind_congr_of_support` for a hypothesis on the support, "
                           "`evalDist_bind_congr mx f g h` for one at every output, or "
                           "`EvalDistEq.bind_congr_of_support` for `=ᵈ`",
    "evalSPMF_bind_congr'": "`evalDist_bind_congr mx f g h`: the continuations are explicit",
    "evalSPMF_bind_congr_left": "`evalDist_bind_congr oa f g h`, or "
                                "`EvalDistEq.bind_congr_of_support` for `=ᵈ`",
    "evalSPMF_bind_const_neverFails": "`EvalDistEq.bind_const`: an oracle computation never "
                                      "fails, so the failure-mass hypothesis goes",
    "evalSPMF_bind_comm": "`evalDist_bind_bind_swap`, or `EvalDistEq.bind_bind_swap` for `=ᵈ`; "
                          "`prrw` swaps adjacent binds inside an event",
    "evalSPMF_map_eq_of_evalSPMF_eq": "`EvalDistEq.map h f` for `h : mx =ᵈ my`",
    "probOutput_bind_mono": "`prEvent_bind_mono_of_forall_le_of_support mx f g p q h`, with the "
                            "events as predicates",
    "probFailure_uniformSample": "`OracleComp.prFail_eq_zero`: an oracle computation never fails",
    "tsum_probOutput_mul_of_const_on_support":
        "`OracleComp.tsum_prEvent_mul_of_const_on_support oa h`: the failure-mass argument goes",
    "tsum_probOutput_mul_le_add_of_le": "`OracleComp.tsum_prEvent_mul_le_add_of_le`, which VCVio "
                                        "provides",
    "probEvent_bind_le_of_forall_le": "`prEvent_bind_le_of_forall_le_of_support mx f q h` for a "
                                      "hypothesis on the support; the arguments are explicit",
    "probEvent_bind_congr": "`prEvent_bind_congr mx f g p q h` for a hypothesis at every output; "
                            "on the support, `wp_congr_of_support` after `prEvent_bind`",
    "probOutput_bind_congr": "`prEvent_bind_congr mx f g (· = y) (· = y) h` for a hypothesis at "
                             "every output; on the support, `wp_congr_of_support`",
    "probOutput_bind_eq_sum_fintype": "`prEvent_bind_eq_sum_fintype mx f (· = y)`: the event is a "
                                      "predicate",
    "withStateOracle_evalSPMF_bind_pure": "`withStateOracle_evalDist_bind_pure`, with measurable "
                                          "spaces on the outputs and the map's measurability",
    "withStateOracle_evalSPMF_map": "`withStateOracle_evalDist_map`, with the map's measurability",
    "abs_probOutput_toReal_sub_le_tvDist": "`absDiff_prEvent_le_etvDist`: the difference of two "
                                           "events' probabilities, in `ℝ≥0∞`",
    "tvDist_bind_right_le": "`tvDist_bind_le mx my f` (`etvDist_bind_le` in `ℝ≥0∞`): the "
                            "continuation is the last argument",
    "tvDist_bind_left_le_const": "`etvDist_bind_bind_le_wp_of_support` with a constant bound, "
                                 "then `wp_le_of_forall_le`",
    "tvDist_bind_left_le_const'": "`etvDist_bind_bind_le_wp` with a constant bound, then "
                                  "`wp_le_of_forall_le`",
    "SPMFSemantics": "`MeasureSemanticsVia`, bundled successful-output measure semantics",
    "toSPMFSemantics": "the field `toMeasureSemanticsVia`, together with `evalDist_map_eq`",
}

# Legacy forms left for a person, with the guide section that converts them.
LEGACY_TOKENS: list[tuple[str, str]] = [
    (r"(?<![\w'])evalSPMF(?![\w'])|𝒮\[", "`𝒟[mx]`; see *Notation and definitions*"),
    (r"(?<![\w'.])probOutput(?![\w'])", "`Pr{let y ← mx}[y = x]` or `𝒟[mx] {x}`"),
    (r"(?<![\w'.])probEvent(?![\w'])", "`Pr{let x ← mx}[p x]`"),
    (r"(?<![\w'.])(?:tvDist_bind_left_le_const'?|tvDist_bind_right_le)(?![\w'])",
     "an `etvDist` bound; see *Lemma names*"),
    (r"(?<![\w'.])(?:SPMFSemantics|toSPMFSemantics)(?![\w'])",
     "the measure semantics; see *Classes and binders*"),
    (r"(?<![\w'.])tvDist_bind_left_le(?![\w'])",
     "`OracleComp.etvDist_bind_left_le_tsum`, with `etvDist` in place of `ENNReal.ofReal (tvDist …)`"),
    (r"(?<![\w'.])expectedValue(?![\w'])", "`∫⁻ x, f x ∂𝒟[mx]`"),
    (r"(?<![\w'.])NeverFail(?![\w'])", "nothing on `OracleComp`; see *Classes and binders*"),
    (r"EvalDistCompatible", "operational support lemmas; see *Classes and binders*"),
    (r"PFunctor\.IsProbabilitySpec|PFunctor\.IsUniformSpec",
     "`PFunctor.AnswerMeasure`; see *Classes and binders*"),
    (r"MeasurableSpace\s*\([^\n]*?\.Range\b",
     "answer measures are discrete; see *Classes and binders*"),
    (r"@(?:OracleSpec\.)?UniformAnswerMeasure\.ofFiniteNonempty\b",
     "takes the specification and its `Finite` and `Nonempty` instances only"),
    (r"(?<![\w'.])SPMF(?![\w'])", "`Measure`; see *Notation and definitions*"),
    (r"(?<![\w'])[\w'.]*?(?:evalSPMF|probOutput|probEvent|probFailure)_[\w'.]*",
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


FUN_TYPED_BINDER = (r"fun\s+\(\s*(⟨[^⟩]*⟩|[^\s():]+)\s*:\s*([^()]*(?:\([^()]*\)[^()]*)*?)\s*\)"
                    r"\s*(?:=>|↦)\s*(.+)")
FUN_BINDER = r"fun\s+(⟨[^⟩]*⟩|[^\s:()]+)(?:\s*:\s*([^=↦]+?))?\s*(?:=>|↦)\s*(.+)"


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


def draw(x: str, comp: str) -> str:
    """The `do` statement `let x ← comp`, parenthesizing a computation spanning several lines."""
    comp = comp.strip()
    if "\n" in comp and not is_parenthesized(comp):
        comp = f"({comp})"
    return f"let {x} ← {comp}"


def singleton(comp: str, value: str) -> str:
    """`Pr{let x ← comp}[x = value]`, with `x` fresh for `comp` and `value`."""
    x = fresh_name(comp, value)
    return f"Pr{{{draw(x, comp)}}}[{x} = {value}]"


def convert_legacy_event(event: str, comp: str, prose: bool = False) -> str | None:
    """The native form of `Pr[event | comp]`, or `None` if the event is not understood.

    In a comment (`prose`), only the syntactic event forms are converted: text such as
    `Pr[ |S| ≤ ℓ ]` is mathematics, not a legacy term."""
    event = event.strip()
    comp = comp.strip()
    if not event or not comp:
        return None
    if event == "⊥":
        return f"prFail {comp}" if is_atomic(comp) else f"prFail ({comp})"
    m = re.fullmatch(r"=\s*(.+)", event, re.S)
    if m:
        return singleton(comp, m.group(1).strip())
    inner = strip_parens(event)
    m = re.fullmatch(r"·\s*=\s*(.+)", inner, re.S)
    if m and "·" not in m.group(1):
        return singleton(comp, m.group(1).strip())
    m = (re.fullmatch(FUN_TYPED_BINDER, inner, re.S)
         or re.fullmatch(FUN_BINDER, inner, re.S))
    if m:
        binder, ty, body = m.group(1), m.group(2), m.group(3).strip()
        if SIMPLE_BINDER.fullmatch(binder) or binder.startswith("⟨"):
            # The binder's type is kept: a numeral in the event would otherwise default to `ℕ`.
            lhs = f"{binder} : {ty.strip()}" if ty else binder
            return f"Pr{{{draw(lhs, comp)}}}[{body}]"
        return None
    if "·" in inner:
        # A section `(· op e)` with one hole: substitute a fresh name for the hole.
        if inner.count("·") != 1 or not event.strip().startswith("("):
            return None
        x = fresh_name(inner, comp)
        return f"Pr{{{draw(x, comp)}}}[{inner.replace('·', x)}]"
    if prose:
        return None
    x = fresh_name(event, comp)
    pred = event if is_atomic(event) else f"({event})"
    return f"Pr{{{draw(x, comp)}}}[{pred} {x}]"


def plain_application(term: str) -> bool:
    """Whether `term` is an identifier applied to identifiers and bracketed groups, which binds
    tighter than `=ᵈ` and needs no parentheses."""
    term = term.strip()
    if is_atomic(term):
        return True
    rest, j = [], 0
    while j < len(term):
        if term[j] in OPEN:
            try:
                j = match_close(term, j) + 1
            except ValueError:
                return False
            rest.append(" ")
            continue
        rest.append(term[j])
        j += 1
    return re.fullmatch(r"@?[^\W\d][\w'.!?₀-₉ₐ-ₜᵢ-ᵪ]*(?:\s+[\w'.!?₀-₉ₐ-ₜᵢ-ᵪ@]*)*",
                        "".join(rest).strip()) is not None


def rewrite_spmf_equations(text: str) -> str:
    """`𝒮[A] = 𝒮[B]` becomes `A =ᵈ B`, unless a side is applied to an argument (a pointwise mass)
    or the left side is itself an argument; a side that is not an application is parenthesized."""
    out: list[str] = []
    i = 0
    while True:
        k = text.find("𝒮[", i)
        if k < 0:
            out.append(text[i:])
            return "".join(out)
        try:
            close = match_close(text, k + 1)
            m = re.match(r"\s*=\s*𝒮\[", text[close + 1:])
            close2 = match_close(text, close + 1 + m.end() - 1) if m else -1
        except ValueError:
            close2 = -1
        before = text[:k].rstrip()
        argument = bool(before) and (before[-1] in ")]}⟩" or re.match(r"[\w'!?₀-₉]", before[-1]))
        after = text[close2 + 1:close2 + 2] if close2 >= 0 else ""
        applied = bool(re.match(r"[ \t]+[\w(⟨@'!?]", text[close2 + 1:close2 + 3])) or after == "("
        if close2 < 0 or argument or applied:
            out.append(text[i:k + 2])
            i = k + 2
            continue
        sides = []
        for term in (text[k + 2:close], text[close + 1 + m.end():close2]):
            term = term.strip()
            sides.append(term if plain_application(term) else f"({term})")
        out.append(text[i:k])
        out.append(f"{sides[0]} =ᵈ {sides[1]}")
        i = close2 + 1


def rewrite_eq_events(text: str) -> str:
    """Write the singleton events `Pr{mx}[= a]` and `Pr{mx}[(· = a)]` of earlier versions of the
    measure API as `Pr{let x ← mx}[x = a]`."""
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
        rest = text[close + 1:]
        m = re.match(r"\[\s*=(?!=)", rest) or re.match(r"\[\s*\(\s*·\s*=(?!=)", rest)
        if not m or not rest.startswith("["):
            out.append(text[i:close + 1])
            i = close + 1
            continue
        try:
            end = match_close(text, close + 1)
        except ValueError:
            out.append(text[i:close + 1])
            i = close + 1
            continue
        value = text[close + 1 + m.end():end].strip()
        if m.group(0).rstrip().endswith("=") and "(" in m.group(0):
            if not value.endswith(")"):
                out.append(text[i:close + 1])
                i = close + 1
                continue
            value = value[:-1].strip()
        comp = text[k + 3:close].strip()
        out.append(f"{text[i:k]}{singleton(comp, value)}")
        i = end + 1


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


DRAW_ITEM = re.compile(r"(\s*)(_|[^\W\d][\w'₀-₉]*)((?:\s*:\s*[^←]+?)?)\s*←(.*)", re.S)


def is_parenthesized(term: str) -> bool:
    """Whether `term` is one parenthesized group."""
    if not term.startswith("("):
        return False
    try:
        return match_close(term, 0) == len(term) - 1
    except ValueError:
        return False


def rewrite_draw_items(text: str, report: Report, path: str) -> str:
    """Write each bare draw `x ← e` of a `Pr{…}` sequence as the `do` statement `let x ← e`.

    A right-hand side spanning several lines is parenthesized, since the layout of a `do`
    statement requires its continuation lines to sit right of the `let`; a sequence continuing
    after such a draw is reported for layout by hand."""
    spans = comment_spans(text)
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
        for n, part in enumerate(parts):
            m = DRAW_ITEM.fullmatch(part)
            if not m:
                continue
            lead, name, ty, rhs = m.groups()
            body = rhs.rstrip()
            trail = rhs[len(body):]
            if "\n" in body and not is_parenthesized(body.strip()):
                # The parenthesis opens on the arrow's line, before the action's first line.
                body = " (" + body.lstrip() + ")"
                if n + 1 < len(parts) and not in_spans(k, spans):
                    report.add(path, text, k, "an event sequence continues after a multi-line "
                               "draw; lay it out as a `do` block, one statement per line")
            parts[n] = f"{lead}let {name}{ty} ←{body}{trail}"
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
    (re.compile(r"\[\s*(?:OracleSpec\.)?IsProbabilitySpec\s+"), "[OracleSpec.AnswerMeasure "),
    (re.compile(r"\[\s*(?:OracleSpec\.)?IsUniformSpec\s+"), "[OracleSpec.UniformAnswerMeasure "),
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
    """Occurrences of the name `name`, except as a quoted Lean name `` `name ``, which denotes
    the name itself (as in a list of retired names) rather than the declaration. A code span
    `` `name` `` in prose is an occurrence."""
    return re.compile(r"(?<![\w'!?])(?:(?<!`)|(?=" + re.escape(name) + r"`))" + re.escape(name)
                      + r"(?![\w'!?₀-₉])")


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


OPEN_LINE = re.compile(r"^([ \t]*open(?:[ \t]+scoped)?)[ \t]+(.*?)([ \t]+in)?[ \t]*$")

# Namespaces that removed modules defined and no remaining import provides.
REMOVED_NAMESPACES = {"OracleComp.EvalDist"}


def rewrite_opens(text: str) -> str:
    """Drop removed namespaces from `open` commands, deleting a command left with none."""
    out: list[str] = []
    for line in text.split("\n"):
        m = OPEN_LINE.match(line)
        if not m:
            out.append(line)
            continue
        names = m.group(2).split()
        kept = [name for name in names if name not in REMOVED_NAMESPACES]
        if kept == names:
            out.append(line)
        elif kept:
            out.append(f"{m.group(1)} {' '.join(kept)}{m.group(3) or ''}")
    return "\n".join(out)


DECLARATION = re.compile(
    r"^[ \t]*(?:@\[[^\]\n]*\][ \t]*)?(?:(?:private|protected|noncomputable|nonrec|partial)\s+)*"
    r"(?:theorem|lemma|def|abbrev|instance|structure|class|inductive)\s+([^\s:({\[]+)", re.M)


def declared_names(texts: list[str]) -> frozenset[str]:
    """The last components of the names the given sources declare."""
    return frozenset(m.group(1).rsplit(".", 1)[-1]
                     for text in texts for m in DECLARATION.finditer(text))


def report_legacy(text: str, report: Report, path: str,
                  local: frozenset[str] = frozenset()) -> None:
    """Report the legacy forms left in `text`. A name in `local`, which the migrated sources declare
    themselves, is reported only where `text` declares it, and only when VCVio has a replacement."""
    spans = comment_spans(text)
    declared_at = {m.start(1) + len(m.group(1)) - len(m.group(1).rsplit(".", 1)[-1])
                   for m in DECLARATION.finditer(text)}
    for regex, hint in LEGACY_TOKENS:
        for m in re.finditer(regex, text):
            if not in_spans(m.start(), spans):
                name = m.group(0).rsplit(".", 1)[-1]
                if name in local:
                    start = m.start() + len(m.group(0)) - len(name)
                    if start in declared_at and name in LEGACY_HINTS:
                        report.add(path, text, m.start(),
                                   f"`{name}` is declared here; VCVio has {LEGACY_HINTS[name]}")
                    continue
                report.add(path, text, m.start(),
                           f"`{m.group(0)}`: {LEGACY_HINTS.get(name, hint)}")
    for name, hint in REPORT_NAMES.items():
        for m in rename_pattern(name).finditer(text):
            if name == "prEvent_le_one" and re.match(r"prEvent_le_one _(?![\w' ]*_)",
                                                     text[m.start():]):
                continue
            if not in_spans(m.start(), spans):
                report.add(path, text, m.start(), f"`{name}`: {hint}")


def migrate(text: str, path: str, report: Report, local: frozenset[str] = frozenset()) -> str:
    text = rewrite_imports(text)
    text = rewrite_opens(text)
    text = rewrite_legacy_events(text, report, path)
    text = rewrite_eq_events(text)
    text = rewrite_spmf_equations(text)
    text = rewrite_draw_items(text, report, path)
    text = delete_answer_binders(text)
    text = rewrite_classes(text, report, path)
    text = rewrite_names(text)
    report_legacy(text, report, path, local)
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
    files = lean_files(args.paths)
    sources = {path: path.read_text() for path in files}
    local = declared_names(list(sources.values()))
    for path in files:
        old = sources[path]
        new = migrate(old, str(path), report, local)
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
