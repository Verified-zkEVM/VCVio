# UC campaign checkpoint — 2026-09-14

> Archived September 14, 2026 evidence from VCVio [#721](https://github.com/Verified-zkEVM/VCVio/pull/721).
> Dependency revisions, restoration commands, and validation counts below describe that dated
> spike. The final v4.34 adoption is integrated through [#710](https://github.com/Verified-zkEVM/VCVio/pull/710);
> use the current manifests and `CONTRIBUTING.md` for builds. The remaining UC adequacy and
> computational-admission obligations below remain separate from the toolchain adoption.

This draft preserves the September 14 dependency adoption spike and the remaining UC campaign
for the September 15 machine-reset handoff. It is a resumable development checkpoint, not a completed toolchain migration
or a claim of full computational UC. Production VCVio remains on Lean/Mathlib 4.33.1.

## Published sources and restoration

| Source | Durable location / revision |
| --- | --- |
| VCVio spike | Branch `audit/uc-rc2-adoption-20260914` in `Verified-zkEVM/VCVio`, containing this document and all VCVio source adaptations |
| PolyFun spike | [Draft #214](https://github.com/Verified-zkEVM/PolyFun/pull/214), commit `bafd63437122bdbc3b852245de58bf4c5b4258df` |
| CSLib constructor fixes | [Fork checkpoint branch](https://github.com/dtumad/cslib/tree/audit/uc-rc2-constructors-20260914), commit `213cd0ce56c640f584edd059b14a3dd77f7a9b8c` |
| Mathlib | `leanprover-community/mathlib4` at `e06eff5f95374108acfaf19f1ff7473aa7771df2` |
| Complexitylib | `SamuelSchlesinger/complexitylib` at `6c248df7859f2f245e731c1e07057bf69d165fe2` |
| Lean | `leanprover/lean4:v4.34.0-rc2` |
| Guarded measure semantics on production dependencies | [VCVio #720](https://github.com/Verified-zkEVM/VCVio/pull/720), head `3d6065060daf6eb2b18e09aba463b9824f96268c` |

The manifests and package configurations use the published immutable Git revisions above.
The optional package retains its intentional relative dependencies on VCVio (`..`) and
VCVio's PolyFun checkout (`../.lake/packages/PolyFun`). No dependency requires the old machine's
temporary directories. The fork's default branch and upstream CSLib were not modified.

Restore the work with:

```bash
git clone --branch audit/uc-rc2-adoption-20260914 https://github.com/Verified-zkEVM/VCVio.git VCVio-uc-rc2
cd VCVio-uc-rc2
lake exe cache get
lake build
lake test
lake exe axiomsweep --check
cd VCVioComplexity
lake exe cache get
lake build VCVioComplexity VCVioComplexityTest
./scripts/check-trust.sh
```

For adoption, regenerate and check the manifests with `lake update --keep-toolchain` in the
root and optional package, and run `./scripts/validate.sh --lint --test --axioms` from the root.
The optional compatibility preflight still describes the production baseline and needs a
deliberate update before it can accept this candidate. Resolve the documented remaining gates
before treating any draft as ready for review or the merge queue.

## Validation already completed

These results were obtained on the identical Lean sources with local dependency checkouts
before replacing the dependency paths with published pins. They are not a claim that the final
Git-pinned checkpoint has passed full validation in a clean clone. The new negative test was
also compiled directly; its umbrella import was regenerated when packaging this checkpoint.
After publishing the pins, PolyFun and the optional VCVio package both resolved their Git
dependencies and passed `lake env lean --version`; the root VCVio umbrella generator also
resolved the fork and completed. These package-loading checks do not replace full validation.

| Check | Result |
| --- | --- |
| CSLib: `lake build --wfail --iofail`, `lake exe mk_all --check`, `lake test`, `lake lint`, `lake exe lint-style`, in that order | All passed. Style lint reported its missing optional nolints file and used an empty baseline. |
| PolyFun: `./scripts/validate.sh --lint --test --axioms` | Passed; 12,046 declarations in 313 production modules, zero sorry or nonstandard axioms. |
| VCVio: production `lake build` | Passed, 4,236 jobs; deprecation warnings remain. |
| VCVio: `lake test` | Passed, including all three test libraries, smoke, and the SLH-DSA executables. |
| VCVio: `lake exe axiomsweep --check` | Passed; 18,893 declarations in 634 modules, unchanged 40 sorry-tainted declarations, zero nonstandard-axiom taint. |
| Guarded fold and positive/negative measurability canaries | Passed on both the production and candidate dependency sets. |
| Optional adapter and all existing canaries | Build passed, 2,682 jobs; kernel trust check passed. |
| Upstream complexitylib composition, combinators, Hoare, output bounds, asymptotics and P definitions | Matched dependency build passed, 2,062 jobs. |
| Production-dependency version of #720 | Full validation passed; 18,923 declarations in 634 modules, unchanged 40 sorry-tainted declarations, zero nonstandard-axiom taint. All nine checks on the published head succeeded. |

The exact old worktree locations were `/private/tmp/vcvio-uc-rc2-candidate-20260914`,
`/private/tmp/polyfun-uc-rc2-candidate-20260914`, and
`/private/tmp/uc-cslib-rc2-candidate-20260914`. Their source work is now preserved in Git.
Temporary caches and full raw build logs are not needed to restore the work; the table above
preserves the results and their limitations.

## Source changes and semantic finding

The PolyFun spike adapts existing draft #184 onto merged #212, including the current bounded-step
API (`RelatesWithinSteps.mono`). Reconcile the two drafts before eventual adoption. The CSLib
fork commit ports the existing FreeM constructor-normal-form fixes from commits `67aabe7` and
`268b2bb` onto `d9be64196bf145edd019f1ccfeaee0c11166ba6b`.

VCVio's compatibility changes move ENNReal imports, remove a redundant proof step, pass
`(← getMCtx)` to `Sym.getMatch` in both tactic registries, supply the new almost-everywhere
measurability argument to `Measure.map_smul`, and repair two support/cache canaries. The new
core registry API can be inspected with `import Lean.Meta.Sym.Simp.DiscrTree` followed by
`#check Lean.Meta.Sym.getMatch`.

The substantive finding is the new Mathlib default for a non-a.e.-measurable pushforward: an
arbitrary Dirac measure. Joining that arbitrary measure does not establish a subprobability
bound. The explicit guard in `VCVio/EvalDist/PFunctorMeasure/Core.lean` interprets an invalid
continuation family as zero and preserves the universal bound. This is an interpretation
convention, not a proof of actual program divergence or abort.

`VCVioTest/MeasurabilityBoundary.lean` gives a finite separating example: every branch is a
Dirac probability measure, yet revealing a bit from a two-point space with only trivial
measurable sets is not a.e. measurable, and the composite is not lossless. Ignoring the same
coarse answer remains lossless. The guard and tests are also published independently in #720;
reconcile that overlapping change when restacking the adoption draft.

## Completed campaign foundations

VCVio #711, #712, #713, #714, #716 and #719, and PolyFun #210–212, are merged. They provide
routed composition and schedule/state transport, executable statistical worlds, separated
single-use OTP with a backchannel, joint handler-law replacement and PRF loss transport,
and global activation-rank certificates with a probabilistic completion bridge. The full
[campaign ledger](uc-campaign.md) records the consumers and negative examples.

#714's cancelled workflows were rerun: all 18 checks on its final head succeeded before it
entered the merge queue. #716 and #719 each had all nine head checks successful before
queueing. Their queue workflows ultimately succeeded. #720 remains a draft; publishing this
checkpoint does not request its merge or enqueue any adoption work. Follow the exact-head
check and merge-queue instructions in `CONTRIBUTING.md` when resuming integration.

The paper repository was not edited by this checkpoint. Literature claims remain bounded by
the proved constructions in the campaign and semantics ledgers.

## Remaining dependency adoption gates

1. Resolve deprecation warnings; run the full VCVio validation sequence, including warning,
   environment lint, import, PMF/exposure, and axiom budgets. Do not suppress linters or increase
   debt to make the upgrade pass.
2. Regenerate and validate final manifests from the published pins in a clean checkout.
   Recheck the upstream-alignment ledgers against these exact commits; #184's older audit
   describes different CSLib/Mathlib revisions in places.
3. Update the optional compatibility preflight and `PROVENANCE.md` for the new baseline.
   Its old known-failure classification is not evidence of machine closure.
4. Reconcile the preservation drafts with #184 and #720, complete review, and require all
   current-head checks to succeed before queueing. A cancelled duplicate remains unresolved
   until rerun, even when another run succeeded.

## Remaining UC implementation plan

1. Prove general operational dummy-adversary/backchannel factorization. Current contextual
   observations compare every finite equal-fuel horizon; charged dummy relays change those
   observations. Supply explicit stuttering/schedule/fuel correspondence or certified completed
   observations rather than erasing relay costs.
2. Give uniform computational admission with one executable code witness across parameters and
   quantifiers `∀ uniform A, ∃ uniform S, ∀ uniform Z`. Fix the simulator before the environment,
   security parameter, and setup. An arbitrary parameter-indexed family is insufficient.
3. Extend the separated OTP consumer to statically indexed sessions with fresh pads and session
   validation, include a cross-session separating example, and prove arbitrary-context
   replacement beyond the current fixed single-use conversation.
4. Prove complete network resource closure: handler costs, routing, queues, scheduling, parsing,
   randomness, initialization/readout, and global feedback bounds. Activation certificates
   alone do not prove machine-work bounds or PPT, and equal laws do not preserve costs.
5. Inhabit the concrete backend's PolyFun category/composition/closure interfaces. Translate or
   deliberately migrate the pair codec: VCVio's empty pair is `[true]`, upstream's is
   `[false, true]`. Existing pure, one-coin and variable-input handler canaries do not implement
   a general compiler or uniform arbitrary-width OTP.
6. Implement one uniform variable-width coin-vector/OTP/simulator on the concrete backend and
   discharge the remaining `CoinBitVecFamily.IsPPTByUnder` code obligation with all-path bounds.

Dynamic corruption, dynamic spawning, infinite-path semantics, and equivalence to a conventional
ITM model remain separate, later adequacy gates. Continue to pair positive consumers with
counterexamples showing where proposed definitions or hypotheses must fail.
