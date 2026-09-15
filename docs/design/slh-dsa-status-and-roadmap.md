# SLH-DSA formalization: status and roadmap

Status: implementation-status report and forward roadmap, established 2026-09-06. It complements
the plan in [`slh-dsa-fips205-generalization.md`](slh-dsa-fips205-generalization.md), which fixes
the target architecture, milestone definitions, acceptance gates, and merge protocol established
on 2026-08-30. This document records what has merged since, what is open, where the plan's snapshot
statements are now stale, and the ordered slices that remain. For the `main` snapshot identified in
the milestone ledger below, use this document rather than the plan's older status statements.

A capability is listed as DONE only when its source and validation are on `main`. Open pull
requests are named as such. No item below should be read as an SLH-DSA security theorem: no
SLH-DSA unforgeability theorem of any kind exists on `main` at the recorded snapshot.

## Where the work lives

| Area | Modules | Validation |
|---|---|---|
| Parameters, positions, addresses, primitive interfaces | `HashSig/SLHDSA/Params.lean`, `FipsParams.lean`, `Position.lean`, `Address.lean`, `Encoding.lean`, `EncodingLemmas.lean`, `Primitives.lean` | `HashSigTest/SLHDSA/Params.lean`, `Position.lean` |
| Components (WOTS+, XMSS, FORS) | `Wots.lean`, `WotsChecksum.lean`, `WotsEncoding.lean`, `Xmss.lean`, `Fors.lean`, `*Conformance.lean`, `Concrete/{Wots,Xmss,Fors,Hypertree}.lean` (checked SHA-2 address domains) | `slhdsa_wots_tests`, `slhdsa_xmss_tests`, `slhdsa_fors_tests`, `HashSigTest/SLHDSA/{Wots,WotsEncoding,Xmss,Fors}.lean` |
| General hypertree and scheme | `HypertreeGeneral.lean` (+ `QueryBound.lean`), `GeneralScheme.lean`, `GeneralSchemeQueryBound.lean`, `DepthOneCompatibility.lean` | `slhdsa_hypertree_tests`, `HashSigTest/SLHDSA/HypertreeGeneral.lean`, `GeneralScheme.lean` |
| Depth-one compatibility scheme | `Hypertree.lean`, `Scheme.lean`, `RandomOracle.lean`, `Oracle.lean` | `HashSigTest/SLHDSA/Hypertree.lean`, `Oracle.lean`, `Scheme.lean` |
| Wire codecs | `Codec.lean`, `Concrete/Codec.lean` | `slhdsa_data_codec_tests` |
| Concrete primitives (12 FIPS sets) | `Concrete/Sha2.lean`, `Concrete/Keccak.lean`, `Concrete/FIPS.lean`, `Concrete/Instance.lean`, `Concrete/Prehash.lean` | `slhdsa_primitive_tests` (+ `PrimitiveVectors/`), `slhdsa_kat` |
| C13 variant (WOTS+C/FORS+C, keccak256, `d = 2`) | `C13/{Params,Primitives,WotsC,ForsC,Xmss,Hypertree,Scheme,Concrete}.lean` | `slhdsa_c13_kat` |
| External interfaces (Alg. 21–25) | `External.lean` | `slhdsa_external_tests` |
| Security packaging | `Security.lean` (primitive families as `TweakableHash`/`PRFScheme`), `MerkleExtractor.lean` | — |
| Security lane, slices 1–5 (on `main`) | `Security/TargetCounts.lean`, `Security/ReachableTargets.lean` (#630); `Security/EncodedTargets.lean` (#631); `WotsInjectivity.lean` (#665); `Security/TraceTargets.lean` (#666); the consolidated second-round review fixes for those four, including `VCVio/OracleComp/QueryTracking/{QueryBound,LoggingOracle}.lean`'s `AllQueriesSatisfy` (#680, `0a1ff722`); `Security/ComponentTraces.lean` (#682, `630301f3`) | `slhdsa_target_ledger_tests`, `slhdsa_encoded_ledger_tests`, `slhdsa_trace_target_tests`, `slhdsa_component_trace_tests` |
| Security lane, slice 6 (open PR, not on `main`) | `Security/CanonicalGames.lean` (PR #683, open) | `slhdsa_canonical_game_tests` (on that branch) |
| Security lane, slices 7–8 (open PRs, not on `main`) | `Security/{WotsWitnesses,ForsWitnesses,XmssWitnesses,HypertreeWitnesses,SchemeWitnesses,HmsgWitnesses,SufResidual}.lean` (#685 → #689 → #692 → #697 → #699 → #700 → #701); `Security/{SchemeGames,Composition,SufBound}.lean` (#708 → #715 → #718); `Security/LimitedProfile.lean` (not yet opened) | `slhdsa_{wots,fors,xmss,hypertree,scheme,hmsg}_witness_tests`, `slhdsa_suf_residual_tests`, `slhdsa_scheme_game_tests`, `slhdsa_composition_tests`, `slhdsa_suf_bound_tests`, `slhdsa_limited_profile_tests` (on those branches) |
| Generic hash games consumed | `VCVio/CryptoFoundations/HardnessAssumptions/TweakableHash/*.lean`, `KeyedHash/ITSR.lean`, `VCVio/CryptoFoundations/SignatureAlg.lean` | `VCVioTest/SMDT*.lean` |

Every SLH-DSA test executable is registered in the `@[test_driver] script test` of `lakefile.lean`
and runs from the single `lake test` step of `.github/workflows/build.yml` (#654 replaced the
per-executable steps). That script builds `VCVioTest`, `LatticeCryptoTest`, and `HashSigTest`
first, which is where the test modules with no executable are compiled, and its output is piped
through `scripts/check-warning-log.py`, so a warning under `HashSigTest/` fails the job like a
proof-library warning does (#679 added the same pass to the local script). `linting.yml` runs
`lake lint -- --style-only`. Since #702, `scripts/lint.py` constructs temporary import roots
covering the proof libraries, `Interop`, and every test module, including leaf test modules.
It passes those roots to the upstream source linter, whose inputs are import lists. This fixes
the coverage limitation recorded in issue #629 item 4. In `build.yml`'s
`check_imported` job, `scripts/check-imports.sh` regenerates every umbrella module and fails if any
of them changes, in place of the former per-library `lake exe mk_all --check` steps, and
`scripts/check-expose-boundary.sh` caps the number of broadly exposed files per library (new
modules use a plain `public section` with per-declaration `@[expose]`); in the build job,
`lake exe axiomsweep --check` guards the axiom and `sorry` footprint against
`scripts/axiom_baseline.json`. `scripts/validate.sh` runs that per-PR gate locally in CI's order,
with `--lint`, `--test`, `--ffi`, and `--axioms` selecting the slower passes.

## Milestone status ledger

Verified against `origin/main` at `82252d83` (2026-09-11).  On 2026-09-15 each of the
fifty-three pull-request numbers this document names — #629 is the follow-up issue, not a pull
request — was re-checked against `origin/main` at `bf181a39` by locating its squash-merge commit
with `git log origin/main --grep='(#N)'` and testing that commit with
`git merge-base --is-ancestor`: thirty-two are ancestors of `bf181a39`, and they are exactly the
numbers this document describes as merged or landed; the remaining twenty-one — those it
describes as open, as closed, or as reverted or replaced before merging — are not.  That is the
whole of what was re-checked; the branch heads and stacking relations quoted for the unmerged
pull requests are as those pull requests last reported them and are not observable from a clone.
The rows outside the lane were carried forward unchanged.

| Milestone | Status | Landed in | Realized by | Gap against the plan's wording |
|---|---|---|---|---|
| G1 valid parameters, all FIPS sets | DONE | #593 | `Params`, `Params.Valid`, `ValidatedParams`, `FipsParameterSet` (12), `LimitedParameterSet`, `FipsParams` | none |
| G2 digest and layer-index calculus | DONE | #595 | `DigestParts`, `splitDigest`, `LayerPosition` (`initial`, `next`, `atLayer`, `toAdrs`), `forsAdrs` | layer is a field of `LayerPosition`, not an index; an allowed normalization |
| G3 intrinsic signature shapes | DONE | #602 | `ForsTreeSigCore`, `ForsSigCore`, `XmssSigCore`, `HtSigCore`, `SignatureCore` | none |
| G4 general hypertree | DONE | #603 | `GeneralHypertree.signM/rootM/pkFromSigM/verifyM`, `verify_sign`, `HypertreeGeneral/QueryBound.lean` | none |
| G5 general internal scheme | DONE | #617 | `keygenInternalM/signInternalM/verifyInternalM`, `verifyInternal_signInternal`, `DepthOneCompatibility` | the depth-one bridge for signing, `signInternalM_toOneLayer_eq`, is not an equality with `slhSignInternalM`: the general signer's trace carries one additional, discarded XMSS recovery. Consumers must use that form |
| G6 exact wire codecs | DONE | #619 | `WireCodec`, `signatureCodec`, `WireLayout.*` slice theorems, `Concrete.approvedWireCodec`, legacy-decoder reconciliation | same-length tamper test at 128f only (issue #629 item 3) |
| G7 SHA2 and SHAKE suites | DONE | #626 | `sha2Primitives`, `shakePrimitives`, `approvedPrimitives`, `Sha2Address`, `sha2AdrsKey_injective_of_domain`, `compressSha2_injective_of_fits` | several primitives, among them SHA-384, SHA-512/224, SHA-512/256, and both MGF1 variants, are regression-pinned rather than covered by independent NIST vectors (`PrimitiveVectors/NOTICE.md`); abstract `F`/`T₁` identification at arity 1 (#629 item 1) |
| FORS and hypertree conformance ports | DONE | #627, #628 | `ForsConformance.lean`, `HypertreeConformance.lean`, typed trajectory traces, concrete address bounds | none |
| G8 external interfaces and prehash | DONE | #611 | `External.lean` (`requireContext`, `signPure*`, `verifyPure*`, prehash variants), `Concrete/Prehash.lean` (12 ACVP names, OIDs), pinned `opt_rand = PK.seed` | "ACVP uses supplied randomness exactly when requested" is untestable until G10 |
| G9 efficient refinement-linked execution | NOT MERGED | frozen branch `feat/slhdsa-g9-efficient-execution-20260831`, tip `0529cefa` (still hosted) | branch-only `HashSig/SLHDSA/Execution.lean` with the full `*_eq_spec` refinement chain | the branch base is 65 commits behind the recorded `main` and carries stale pre-merge copies of the G4–G8 files; re-slice it instead of rebasing the whole branch (see below) |
| G10 ACVP and KAT coverage | NOT MERGED | frozen branch `feat/slhdsa-g10-acvp-kat-20260831`, tip `f14a9a5e` (still hosted) | branch-only ACVP schema, strict JSON parser, lossless corpus pinned to ACVP-Server `975de31e`, provenance scripts | the branch parses vectors but executes none; on `main` the only whole-scheme KATs are `Sha2KAT.lean` (one SHA2-128-24 vector) and `C13KAT.lean` |
| CF1 final-validity games | DONE | #594, #622, #624 | `TweakableHash/FinalValidity.lean`, `SMDTTCRFinalValidity`, `SMDTPREFinalValidity`, `ToFinalValidity.lean` | none |
| CF2 DSPR, OpenPRE, UD, ITSR | DONE | #596, #623, #625 | `SMDTDSPRFinalValidity`, `SMDTOpenPREFinalValidity`, `SMDTUDFinalValidity` (message-subspace parameter), `KeyedHash/ITSR.lean`, `OpenPREFromTCRDSPR.lean` (`toTCR`, `toDSPR`, `CountingInterface`) | the OpenPRE probability coupling remains an explicit interface, as the plan allows |
| CF3 generic SUF surface | DONE | #601 | `SignatureAlg.strongUnforgeableAdv`, `sameMessageAdvantage`, `advantage_eq_euf_add_sameMessage` | SLH-DSA must use the per-adversary partition, not `SameMessageBinding` (#629 item 2b) |
| D1A target and address ledger | PARTIAL: slices 1–5 DONE | #630 (`a19548d2`), #631 (`b7d06dff`), #665 (`81a75e90`), #666 (`67b3a6d9`), merged 2026-09-07/08; #680 (`0a1ff722`) and #682 (`630301f3`), merged 2026-09-12 | slices 1–5 of the security lane below; slice 6 is open as PR #683 | `Params.IsD1` unclaimed, and deliberately so — see the corrections below; the canonical game instances are not on `main` |
| D1B witness translations | IN REVIEW | — | slice 7 below, in seven pull requests: #685, #689, #692, #697, #699, #700 and #701, open and stacked in that order, none merged. Slice 8 consumes five of the seven modules by name — twelve declarations of the SUF residual, seven of the scheme dispatch, two each of the `H_msg` and hypertree families and one of the FORS one, and none of the WOTS+ or XMSS ones, counting the declarations of each slice-7 module whose own name occurs as an identifier in the four slice-8 library modules with comments and docstrings stripped, so that the three reached only through dot notation (`Witness`'s two constructors and `HmsgIndex.forsAdrs`) are not among them — and is itself unmerged. On `main` only `SLHDSA.xmssPkFromSig_binding` exists, as a deterministic hook | the #585 lemmas are stated against the pre-G3 depth-one scheme; and no family extracts from the second branch of #701's partition, so the same-randomizer case has no witness at all |
| Rewritten #585 (conditional quantitative theorem) | IN REVIEW | — | slice 8 below, in four pull requests: #708, #715 and #718 are open and stacked in that order, and the SHA2-128-24 profile corollary with this document's refresh is the fourth and is not yet opened. Nothing is on `main` | the theorem is conditional on a `Certificate` that no proof in the repository supplies and that costs an address key and a public seed to build, so it bounds the advantage by a named expression and not by anything small; #585 is an archived donor, see below |
| Merkle integration, general-`d` security | NOT STARTED | Merkle PRs #574, #575, #577–#579, #586–#591 merged | `MerkleExtractor.lean` is a log projection only; nothing under `HashSig/` imports `MultiExtractability` | all five integration bullets of the plan are absent |

### Gate status

- **General formalization gate (G1–G5): met.** Arbitrary validated `d`, intrinsic shapes, complete
  digest and layer recurrence, composing oracle-parametric and deterministic interpretations,
  general-`d` perfect completeness (`GeneralScheme.verifyInternal_signInternal`), explicit
  depth-one specialization. The random-oracle `PerfectlyComplete` packaging exists only for
  `d = 1` (`SLHDSA.slhdsaAlg_perfectlyComplete` in `RandomOracle.lean`); no general-`d`
  `SignatureAlg` packaging exists.
- **FIPS conformance gate (G6–G10): not met.** Twelve sets instantiated, formulas executable,
  codecs strict, interfaces match Algorithms 18–25, and 128f runs end to end through the
  specification path. Missing: the pinned ACVP corpus is not executed anywhere, no
  refinement-linked optimized path is on `main`, and no benchmark record exists for the six
  numerical shapes.
- **`d = 1` security gate: not met, in progress.** #630, #631, #665, #666, #680 and #682 are on
  `main`: the ledgers and their encoded form, the WOTS encoding injectivity theorem, and the
  component trace contracts. They use the general scheme without a duplicate implementation and
  disclaim security content. Missing on `main`: the canonical game instances (slice 6, open as
  PR #683), every witness translation (slice 7, seven open pull requests), and all of slice 8.
  A profile-specific statement for SHA2-128-24 beyond the encoded-ledger conditions now exists in
  review — `Security/LimitedProfile.lean` instantiates the twelve-summand EUF-CMA expression and
  the strong-unforgeability headline at the SP 800-230 reduced set, discharging nine carrier
  instances and turning the `w − 2` coefficient into the numeral 2 — and it does not move this
  gate. Read what it establishes exactly: the **shape** of `EUFCMA_SPHINCS_PLUS`'s right-hand
  side, twelve named advantages in the source's order at the source's coefficients, conditional
  on a `Certificate` whose eleven adversaries are quantified with nothing tying any of them to
  the adversary being bounded. At that profile as at every other, a closed certificate is
  constructible from an address key and a public seed, and the fixture builds one and proves the
  bound it names is at least one. So no summand is bounded, no reduction adversary exists, and
  nothing about SLH-DSA-SHA2-128-24's security follows from the corollary. What this gate needs
  is the twelve reduction adversaries, which are the bulk of the EasyCrypt development and are
  not begun.
- **General-`d` security gate: not started**, and correctly claimed nowhere.

## Security lane: slices, status, and source correspondence

The lane follows the plan's D1A → D1B → conditional theorem order, stated for arbitrary `d` with
`d = 1` as corollaries, and mirrors the structure of the EasyCrypt proof of SPHINCS+ (Barbosa,
Dupressoir, Hülsing, Meijers, Strub; `SPHINCS_PLUS.ec`, `WOTS_TW_ES.ec`, `FORS_ES.ec`,
`FL_SL_XMSS_MT_ES.ec`). Slices 1–5 are on `main`: the stack #630 → #631 → #666 and the
independent WOTS encoding proof #665, which later reduction slices both consume, together with
their consolidated second-round review fixes #680 (`0a1ff722`) and the component trace contracts
#682 (`630301f3`), all merged by 2026-09-12. Slice 6 is open as #683. Each slice is its own
pull request, stacked on the previous one where it depends on it,
opened as a draft, adversarially reviewed on every commit by an independent read-only reviewer,
and taken out of draft only when a review round reports nothing to fix. The recurring defect
class across every review round so far has been prose claiming more than the lemmas prove;
reviewers check each docstring sentence against the lemma it describes.

| # | Slice | Content | Status | EasyCrypt counterpart |
|---|---|---|---|---|
| 1 | Target roles, counts, structural ledgers | `TargetRole` (8), `targetCount`, `xmssTreeCount`, `wotsInstanceCount`; executable `List Adrs` ledgers per role with exact `length` (or honest upper bound for the WOTS+ TCR and PRE roles), `Nodup`, `mem_*` completeness, pairwise disjointness; `EncodedTargetLedgerConditions` | merged 2026-09-07 (#630, `a19548d2`) | clone parameters `t_smdtud = t_smdtpre = c·len`, `t_smdttcr = c·len·w` (`WOTS_TW_ES.ec`), `d·k·t`, `d·k·(t−1)`, `d` (`FORS_ES.ec`, with `d = 2^h` under the `SPHINCS_PLUS.ec` instantiation), the two hypertree sums (`FL_SL_XMSS_MT_ES.ec`); `c = wotsInstanceCount` |
| 2 | Encoded ledgers | SHA-2 compressed-address domain (`CanonicalAddressBounds`, `ApprovedAddressBounds`, `Sha2Domain`), per-ledger membership, `approvedEncodedTargetLedgerConditions` for all twelve sets and both encoders, `limitedEncodedTargetLedgerConditions`; counterexample profile pinned as `deep_sha2_conditions_false` | merged 2026-09-07 (#631, `b7d06dff`); was stacked on #630 | type-tag distinctness side conditions (`dist_adrstypes`, `get_typeidx … <> chtype` preconditions) |
| 3 | WOTS message-encoding injectivity | `Function.Injective` of the full-width `wotsMsgDigitsCore` under `p.Valid` (which supplies `lgw ∣ 8n`) and `core.ByteLaws`, from `WotsChecksum.fromBaseW_digitsOfBaseW_of_lt`; lifts `wots_fullDigits_incomparable` to `core.Y` | merged 2026-09-07 (#665, `81a75e90`); independent of the stack | axiom `two_encodings` (`WOTS_TW_ES.ec`), the only encoding fact the source assumes |
| 4 | Trace provenance (WOTS+) | `constructionAddresses` union ledger with `Nodup`, `QueriesWithinConstructionTargets` pathwise `IsQueryBound` over `publicHashSpec`, theorems for `chainM`, `wotsPkGenM`, `wotsSignM`, `wotsPkFromSigM`, the logged-execution bridge for any `QueryImpl (publicHashSpec core) Id` | merged 2026-09-08 (#666, `67b3a6d9`); was stacked on #631; port of the archived donor with the enumeration-completeness section replaced by slice 1's `mem_*` lemmas; the public membership and encoding equations its consumers need, and the restatement of the wrapper as VCVio's `AllQueriesSatisfy`, are in #680, merged 2026-09-12 | the `hoare` address-discipline lemmas on the WOTS-TW oracles |
| 5 | Trace provenance (FORS, XMSS, hypertree, scheme) | predicate-tracking Merkle lemmas added to VCVio (`PerfectMerkleTree.merkleRootM_pred_of_subtree`, `intrinsicAuthPathM_pred_of_siblings`, `intrinsicAuthPathM_pred_of_tree`, `climbM_pred_of_ancestors`, `AddressedMerkleTree.getPutativeRootAddressedM_pred_of_ancestors`), instantiated as `QueriesWithinConstructionTargets.merkleRootM/intrinsicAuthPathM/climbM`; twenty-two `*_queriesWithinConstructionTargets` theorems, covering `forsRootM`, `forsPkGenM`, `forsSignM`, and `forsPkFromSigM` (the last three also at the address Algorithm 19 derives from a digest), `xmssLeafM`, `xmssNodeM`, `xmssRootM`, `xmssSignM`, `xmssPkFromSigM`, the typed hypertree loops `signFromPositionM` and `recoverFromPositionM`, their entry points `GeneralHypertree.signM/pkFromSigM/verifyM/rootM` (named `hypertreeSignM_…` and so on), and `GeneralScheme.keygenInternalM/signInternalM/verifyInternalM`; twelve `*_traceContract` theorems pairing FORS public-key generation, signing and recovery, the four XMSS programs, hypertree signing and recovery, and the three internal scheme programs with an `IsTotalQueryBound`, closed-form at the FORS and XMSS levels and the `HypertreeGeneral.QueryBound`/`GeneralSchemeQueryBound` bounds — upper bounds, not exact counts — at the hypertree and scheme levels | merged 2026-09-12 (#682, `630301f3`); was stacked on #680 (`Security/ComponentTraces.lean`, `HashSigTest/SLHDSA/ComponentTraces.lean`, `slhdsa_component_trace_tests`); derived, no donor | the corresponding FORS/XMSS/hypertree oracle lemmas |
| 6 | Canonical game instances | source-final-validity `Problem`s over the tweak space `Primitives.AdrsKey`, split standalone versus collection as the source is: three standalone FORS-`F` games with no collection oracle (`Problem.standalone` at collection index `Empty`) — OpenPRE, DSPR, and TCR — the latter two shown equal to `.toDSPR`/`.toTCR` of the OpenPRE problem (`forsFDsprProblem_eq_toDSPR`, `forsFTcrProblem_eq_toTCR`), and seven collection games sharing `Primitives.thashCollection`: TCR for FORS `H`, FORS `T_k`, WOTS+ `F`, WOTS+ `T_len`, and XMSS `H`, and UD and PRE for WOTS+ `F` with the whole node type as the subspace and the identity embedding. The seven collection records are `@[expose]`d so a downstream collection query type-checks; the standalone ones and the `H_msg` family stay opaque behind exported equations. ITSR for `H_msg`, keyed by the message randomizer and indexed by `hmsgIndices` (`splitDigest` locates the FORS instance, `forsIdx` reads each tree's leaf, `k` indices per digest); `numTargets := targetCount p role` bridges; no reductions and no inequalities | PR #683 (open), head `731bd820` on `feat/slhdsa-d1a-canonical-games-20260907`, opened stacked on #682 in the PR chain, which has since merged, and importing nothing from slice 5 (`Security/CanonicalGames.lean`, `HashSigTest/SLHDSA/CanonicalGames.lean`, `slhdsa_canonical_game_tests`); port of the archived donor `CanonicalGames.lean` retargeted to the game modules of #623–#625 | `FP_DSPR`, `FP_TCR`, `TRHC_TCR`, `TRCOC_TCR`, `FC_UD`, `FC_PRE`, `FC_TCR`, `PKCOC_TCR`, `MCO_ITSR` clones; two recorded deviations from `MCO_ITSR`: the source's `MCO` hashes the message alone while this input carries `PK.seed` and `PK.root` as FIPS 205 Algorithm 19 does, so at any fixed `PK.seed` and `PK.root` the instantiated assumption implies the source's, and the source's flat instance index is split into the `(idxTree, idxLeaf)` pair `splitDigest` produces |
| 7 | D1B witness translations | deterministic forgery-to-witness translations over `GeneralScheme` and the intrinsic vectors, every statement labeled deterministic inclusion or transcript transport: `Security/WotsWitnesses.lean` (chain forgeries), `Security/ForsWitnesses.lean`, `Security/XmssWitnesses.lean`, `Security/HypertreeWitnesses.lean` (the layer walk), `Security/SchemeWitnesses.lean` (the pure `keygenInternal`/`verifyInternal` equations, the two-way split on the recovered FORS public key, and the `Witness` dispatch with its computable extractor), `Security/HmsgWitnesses.lean` (the `H_msg` index-to-FORS-coordinate maps, the widening of the hashed input stated in both directions, the first-uncovered-index extractor and the win-or-uncovered dichotomy), and `Security/SufResidual.lean` (the deterministic strong-unforgeability residual: a signing log read at one message, and the partition of a strong forgery by whether its randomizer occurs there). No probability, adversary, advantage or game hop anywhere | seven pull requests, none merged: #685 → #689 → #692 → #697 → #699 → #700 → #701 are open, the last being the SUF residual's. The #585 lemmas were the idea source only | the `valid_TCRTRH` and chain-consistency case analyses; the FORS case split is a reordering of `FORS_ES.ec`'s, not a restriction; and the residual has no counterpart at all, the source having no strong-unforgeability game |
| 8 | Composition and conditional theorem | the two instrumented experiment splits and the named halves they define — the EUF dispatch split at the recovered FORS public key and the same-message split at whether a forgery's randomizer was logged (`Security/SchemeGames.lean`); the composition certificate, the exact conditional EUF-CMA expression (twelve summands with the `3·` and `(w−2)·` coefficients), the OpenPRE-to-`DSPR + 3·TCR` coupling that is the one step of its proof which is not arithmetic, and the two transports onto slice 6's standalone FORS-`F` games (`Security/Composition.lean`); the strong-unforgeability residual bound, with the two equivalences saying that the residual written on the right is the residual already inside the left (`Security/SufBound.lean`); and the SP 800-230 profile corollary, with the nine carrier instances, the eight caps as numerals and the undetectability coefficient as `2` (`Security/LimitedProfile.lean`). The certificate is free — a closed one is constructible from an address key and a public seed at every validated parameter set and every bundle carrying the nine carrier instances it asks for, which the composition, strong-unforgeability and profile fixtures each build and ship as a canary — so what is proved is the shape of the source's expression and not yet a statement about SLH-DSA's security. The program-equivalence hops and the OpenPRE counting interface are named hypotheses; the same-randomizer half of the residual has no bound and no source counterpart | four pull requests, none merged: #708 → #715 → #718 are open and stacked in that order, and the profile corollary with this document's refresh is the fourth and is not yet opened. Replaces #585 | `EUFCMA_SPHINCS_PLUS` (`SPHINCS_PLUS.ec`); no counterpart for the SUF residual, whose absence slice 7 records |

Hypotheses the conditional theorem is expected to carry explicitly, each corresponding to an
undischarged or program-level step in the source proof:

- the two PRF hops (`SKG`, `MKG`) against `skPrfScheme`/`msgPrfScheme`, with no NPRF scheme
  variant yet on `main`;
- the FORS public-key recomputation-versus-recovery program equivalence over `signInternalM`
  (`SLHDSA.forsPkFromSig_forsSign` supplies the deterministic identity over `Primitives`; the
  monadic lift over `signInternalM` is the hypothesis);
- the `(w − 2)` UD hybrid, for which VCV-io has no hybrid-argument machinery, so slice 8 carries
  the coefficient as a literal rather than deriving it;
- the OpenPRE-from-TCR/DSPR probability coupling
  (`SM_DT_OpenPRE_SourceFinalValidity.CountingInterface`) — specifically its two mass equations
  and its strata inequality, which VCV-io's own docstring calls the substantive probabilistic
  coupling still to be constructed;
- **correction**: uniform full-digest distribution for the FORS inputs
  (`Problem.HasUniformInputs`) was listed here as a hypothesis the theorem carries, and it is
  not. As a `Problem` field it is discharged by slice 6 — `forsFOpenPreProblem_hasUniformInputs`
  proves it by `rfl` — and slice 8 uses it to fill the counting interface's `uniformInputs`
  field, the one field of that interface which is not an obligation. What does remain a
  hypothesis is the modelling fact that honest FORS leaf preimages are uniform, and that lives
  inside the two PRF hops rather than beside them;
- structural adversary query bounds. Slice 8 adds one that the plan did not foresee: the
  `MCO_ITSR` summand carries no target cap at all, because `KeyedHash.ITSRProblem` has two fields
  and neither bounds the transcript, so the Lean advantage is a supremum over adversaries with
  unbounded target transcripts where the source's term is bounded through its reduction;
- the same-randomizer half of the strong-unforgeability residual, which has no counterpart in the
  source at all and no bound anywhere in this repository.

Reduction traps recorded in issue #629 apply to every slice from 6 onward: the zero fallbacks of
`sha2AdrsKey` and `checkedNodeOrZero` alias reachable values, so every statement carries the
checked-domain hypotheses of `sha2AdrsKey_injective_of_domain`; and `SameMessageBinding` is
unbounded, so the SUF residual uses `advantage_eq_euf_add_sameMessage`.

### Design decisions settled during review

- Two bounds records rather than one: `CanonicalAddressBounds` (what SHAKE needs) and
  `ApprovedAddressBounds extends` it (two compressed widths for SHA-2). A single record with a
  docstring excusing the too-strong SHAKE hypothesis was rejected; the separating profile is a
  regression test.
- Ledger completeness lemmas are named `mem_<ledgerName>`.
- Per-role ledgers mirror the source's separate clones; games that share a hash function
  (arity-1: WOTS `F` and FORS `F`; arity-2: XMSS `H` and FORS `H`; `T_ℓ`: WOTS public key and FORS
  roots) rely on the pairwise disjointness lemmas of slice 1 when a union target list is needed.
- Final-validity games are instantiated, as in the source; `ToFinalValidity.lean` bridges the
  reject-on-arrival problems that `Security.lean` packages today (`thashTcrProblem`,
  `thashPreProblem`).

## Frozen branches: G9 and G10

The G9 and G10 branches, `feat/slhdsa-g9-efficient-execution-20260831` (tip `0529cefa`) and
`feat/slhdsa-g10-acvp-kat-20260831` (tip `f14a9a5e`), are still hosted but frozen: both tips
predate the merged G4–G8 and carry stale pre-merge copies of those files, so neither can be
rebased. Use the tip commits as idea sources and re-slice only the owned changes:

- **G9**: a single PR carrying `HashSig/SLHDSA/Execution.lean` (the `treeHash`,
  `authenticationPath`, and `*_eq_spec` refinement theorems restated against the merged
  `GeneralScheme`, `Codec`, and `External` APIs) plus `HashSigTest/SLHDSA/Execution.lean` and a
  benchmark record for the six numerical shapes.
- **G10**: first a corpus-import PR (schema, strict JSON parser, lossless corpus, manifest pinned
  to ACVP-Server `975de31e`, provenance check script), then a runner PR that executes
  `keygenWithSeeds`, `signPure*`, and `verifyPure*` on every group of the corpus, with CI running
  the smoke subset and the full corpus on a schedule.

These are maintainer-owned lanes; the security lane does not depend on them.

## Disposition of PR #585

#585 stays open as a draft on the merged base `repair/multitarget-collection-20260828` with the
pre-G3 depth-one scheme. Nothing in the live security lane reuses its branch. Its
`Security/ReductionBound.lean`, `Concrete/Security.lean`, and witness lemmas in `Security.lean`
are idea sources for slices 7 and 8, which will be new pull requests. The plan's statement that
#585 "retains its number" should be read as: the rewritten theorem replaces it, and #585 is closed
with a cross-reference when slice 8 opens.

Slice 8 has opened — #708, #715 and #718, with the profile corollary pending — so that condition
is met and the cross-reference exists. Two things about it are worth writing down before anyone
acts on it, and only the first bears on the timing. The replacement is four pull requests and
**none of them is on `main`**, so closing #585 now removes the only description of the donor's
`Concrete/Security.lean` while its replacement is still under review. The second is a requirement
on the closing comment rather than a reason to wait: the replacement claims less than #585's own
description does — that description lists a "concrete SHA2-128-24 conditional EUF-CMA theorem
with the WOTS coefficient reduced to exactly `2`", which is what `Security/LimitedProfile.lean`
now states, but the lane has since measured that the certificate such a theorem is conditional on
costs an address key and a public seed, so the statement is about the shape of the source's
expression rather than about the profile's security. The recommendation from slice 8 is therefore
to close #585 when slice 8's last pull request merges, or when the stack is abandoned, whichever
comes first — not when it opens — and for the closing comment to name the four replacements, say
that none is merged yet, and record that the replacement theorem is conditional in that specific
way.

## Corrections to the plan document

Statements in `slh-dsa-fips205-generalization.md` that are snapshots of 2026-08-30 and are no
longer true on `main`:

- "Planning baseline" and the "reduced-profile boundaries" list (`h = d·hp` unenforced, digest
  split without the tree index, one-XMSS `HtSigCore`, 3,856-byte decoder, empty-context wrapper):
  every bullet is resolved by G1–G8.
- "The Merkle stack runs from #574 through #591 … not a prerequisite": the Merkle PRs in that
  range (#574, #575, #577–#579, #586–#591) all merged 2026-09-01; the current Merkle work is
  #618 and #621.
- The pull-request stack table names no PR numbers. For the record: G5–G8 landed on `main` through
  #617, #619, #626, and #611. Of the original stacked PRs, #604–#606 were closed and #607 was
  squash-merged into the stacked G7 branch by mistake and reverted there (its content reached
  `main` through #611); #627 and #628 carried the FORS and hypertree conformance ports in place of
  #608 and #609.
- "D1A: d1 target/address ledger": #630 states the ledgers for arbitrary `d`; the depth-one values
  are corollaries.
- `Params.IsD1` is named as a D1A deliverable but does not exist; `main` threads `p.d = 1`
  hypotheses directly (`DepthOneCompatibility` and `Security.xmssTreeCount_of_d_eq_one`, both on
  `main`). The choice this document left open — add the predicate in slice 8, or amend the
  plan — is settled by amending the plan: slice 8 states its headline for arbitrary `d` over
  `GeneralScheme`, and the only depth-one object in it is the SP 800-230 profile, where `d = 1`
  is a checked fact of the parameter set (`Security.limitedParams_d`) rather than a threaded
  hypothesis. A one-field predicate that nothing threads would be worse than the `p.d = 1`
  hypotheses `main` already carries, so `Params.IsD1` is not added.
- The plan does not mention the archived donor at commit `88314278` (closed #597; still hosted
  as the remote branch `archive/slhdsa-pr597-final-88314278`), whose
  `Security/{CanonicalGames,TraceTargets,Architecture}.lean` were the inputs of slices 4 and 6,
  both now consumed, nor the follow-up issue #629.

## Follow-ups outside the security lane

- Issue #629: abstract `F`/`T₁` identification, reduction-checklist items, all-profile
  same-length wire-tamper test, two doc nits.
- `HashSigTest/SLHDSA/GeneralScheme.lean` says no executable `d > 1` primitive instance exists;
  `DataCodecTests`, `External`, and `HypertreeConformanceTests` now execute SHA2-128f (`d = 22`).
- The depth-one compatibility signer (`slhSignInternalM`) and the general signer coexist, related
  by `signInternalM_toOneLayer_eq`. The plan forbids keeping both indefinitely; the compatibility
  scheme should be retired once slice 7 consumes `GeneralScheme` directly.
- Independent NIST vectors for the regression-pinned primitives listed in
  `HashSigTest/SLHDSA/PrimitiveVectors/NOTICE.md`.
- Deferred cleanup ledger from the stack reviews: the `XmssSig` alias of `XmssSigCore`, the dead
  `pk` parameter of `recoverFromPositionWith`, the unused `FipsParameterSet.category`, and the
  smaller items recorded in the review threads of #605–#611.

## Working protocol for the lane

- Branch from the previous slice's head, `feat/slhdsa-<slice>-YYYYMMDD`; open as a draft PR
  immediately; push regular commits.
- Per slice, the gate is `./scripts/validate.sh`, which runs the per-PR CI checks in CI's order:
  the seven-library build with its non-`sorry` warning budget, `scripts/check-imports.sh`, the
  PolyFun, PMF/SPMF, broad-expose, complexity-backend, `Extern` and `Interop` boundary ratchets,
  `lake lint -- --style-only` over the libraries and every test module, and
  `python3 scripts/check-agent-docs.py` with `extract-doc-fragments.py --check`. Add `--test` for
  `lake test` (the three test libraries, the smoke test, and every SLH-DSA executable, with the
  test-library warning budget applied to its log) and `--axioms` for `lake exe axiomsweep --check`
  before pushing a slice; `--lint` adds the Batteries environment linters. While iterating,
  `lake build HashSig HashSigTest` and the slice's own executable are the short loop, and
  `git diff --check` runs on every commit.
- Every commit gets an independent read-only adversarial review that cross-checks against FIPS 205,
  the EasyCrypt artifact, and the reference implementation; findings are validated, fixed, and the
  dispositions posted on the PR. Docstring changes are re-read sentence by sentence against the
  lemma they describe before pushing.
- Author-owned PRs need a second maintainer's approval; a stacked PR is added to the GitHub merge
  queue only after its predecessor has merged and GitHub has retargeted it to `main`.

## References

- NIST FIPS 205, *Stateless Hash-Based Digital Signature Standard*, August 2024. Section map
  used by the lane: §4.1 hash functions and PRFs, §4.2 addresses, §5 WOTS+ (Algorithms 5–8),
  §6 XMSS (9–11), §7 hypertree (12–13), §8 FORS (14–17), §9 internal functions (18–20),
  §10 external functions (21–25), §11 parameter sets (§11.2 compressed address `ADRSc`,
  Figure 18, Table 3).
- M. Barbosa, F. Dupressoir, A. Hülsing, M. Meijers, P.-Y. Strub, *A Tight Security Proof for
  SPHINCS+, Formally Verified*, ASIACRYPT 2023; EasyCrypt development `FV-SPHINCSPLUS-EC`.
- D. J. Bernstein, A. Hülsing, S. Kölbl, R. Niederhagen, J. Rijneveld, P. Schwabe, *The SPHINCS+
  Signature Framework*, CCS 2019; SPHINCS+ round-3.1 specification (2022) and NIST submission
  package (reference implementation).
- A. Hülsing, J. Rijneveld, F. Song, *Mitigating Multi-Target Attacks in Hash-Based Signatures*,
  PKC 2016.
- NIST ACVP-Server SLH-DSA vectors, commit `975de31e`.
