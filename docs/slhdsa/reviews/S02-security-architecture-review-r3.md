# S02 independent security-architecture review r3

Verdict: **FAIL**

Blocking findings: **4**
Nonblocking findings: **0**

Reviewer: fresh independent S02 r3 reviewer; not the S02 implementer.
Review date: 2026-08-25.
Reviewed tree: VCVio commit `c5d6cb03d11126e6290bec58ef8824f36fc3a73b` on branch
`codex/sphincsplus-formalization`, plus the current uncommitted S02 worktree.

Independence and write-scope statement: I began from the pinned EasyCrypt programs, the current
Lean types, the two current S02 documents, and the r1/r2 counterexamples and dispositions. Read-only
commands and a new `/tmp/S02R3IndependentProbe.lean` were the only actions before this verdict.
This r3 file is my only repository edit. I did not alter the implementation, `HashSig.lean`, either
S02 design/session document, the r1/r2 artifacts, accepted S00/S01 infrastructure or harness, or the
rejected legacy `HashSig/SLHDSA/Security.lean`.

## Decision summary

R3 contains genuine local repairs. Construction origins now distinguish eight roles and have a
compiled cardinality guard. Package-level collection separation was moved into the `-C` events.
The FORS DSPR and SPprob expressions invoke the same Lean function and use its selected index. The
WOTS UD real handler returns an output rather than a preimage, both UD worlds log target-oracle
queries, and the event checks the logged count and distinctness. The ITSR term now has a fresh-key
default oracle and a dedicated history. The exact twelve visible summands, coefficients, count
formulas, generated-key coupling in the original EUF experiment, actual query predicates, and
classical-only boundary remain intact. All builds and the axiom gate pass.

Those improvements do not yet produce the pinned component games. The honest-target provider is
uninhabitable for a valid no-query adversary because the distribution has an empty log while every
certified outcome requires eight positive construction-origin families in that log. The
TCR/DSPR/PRE terms are post-processors of a completed original-scheme transcript rather than
target-oracle adversaries run inside the component games. The WOTS UD-C real input distribution and
collection trace are not the source game's same-execution semantics. Finally, the standalone ITSR
program is supplied a full PRF-generated SLH key pair, whereas the named post-SKG/post-MKG
EasyCrypt reduction constructs the NPRF M-FORS key material inside the ITSR adversary.

These are load-bearing experiment and inhabitation defects, not missing proofs of an otherwise
source-equivalent statement. S02 cannot be accepted in r3.

## Blocking findings

### S02-R3-001 — the honest-target provider is uninhabitable for an admitted no-query adversary

`CertifiedHonestOutcome` requires a `CertifiedTargetPackage` for every one of the eight positive
roles (`HashSig/SLHDSA/Security/Architecture.lean:273-277`). Every package requires every indexed
target to occur as a matching `.construction role` query in the sample log
(`Architecture.lean:202-263`). But the distribution to which the provider marginal is equated can
never generate such an event in the current implementation:

- `adversaryQueryImpl` tags every public `F`, `H`, and `Tl` request as `.adversary`
  (`HashSig/SLHDSA/Security/OracleSurface.lean:151-162`);
- a public signing request is logged only as the outer `.sign` event, and `queryImpl` runs
  `slhSign` as an opaque `ProbComp` without emitting internal execution queries
  (`OracleSurface.lean:191-204`, `Transcript.lean:139-146`);
- the current documentation confirms that the signer exposes no internal primitive trace
  (`docs/slhdsa/security-architecture.md:118-121,186-188` and
  `docs/slhdsa/sessions/S02-security-architecture.md:159-163`).

The independent probe compiled both halves of a direct counterexample. First, a no-query public
adversary definitionally has the honest distribution

```lean
honestTranscriptDistribution prims encode (noQueryAdversary forgery) = do
  let keys ← generateKeyPair prims
  return ⟨keys, ({ forgery := forgery, log := [] } : Transcript keys)⟩
```

by `rfl`. Second, for every parameter-valid sample with `sample.2.log = []` and every role,

```lean
¬ Nonempty (CertifiedTargetPackage prims conditions sample role)
```

follows by selecting index zero from `positiveTargetCount` and reducing `TargetObserved`; all eight
cases contradict the empty log. `HonestTargetProvider.marginal` nevertheless requires its
certified distribution, for this same adversary, to erase exactly to that empty-log distribution
(`Architecture.lean:418-427`). It cannot drop the outcome, replace its transcript, or attach the
required certificate.

Thus `ClassicalSecurityContext.targets` is not merely awaiting a difficult construction: its
current universally-adversarial marginal and current logging semantics are incompatible. The
explicit future-refinement caveat is accurate, but it confirms an impossible load-bearing context
under the code being proposed for acceptance. This is the impossible-hypothesis/type-vacuity class
that `docs/slhdsa/review-protocol.md:15-17` requires the review to reject.

### S02-R3-002 — TCR, DSPR, SPprob, and PRE are post-hoc transcript events, not the named oracle games

The authoritative target games run the reduction *inside* a challenger interaction. For example:

- SM-DT-PRE initializes the target oracle, runs `A.pick()` with `O.query`, then runs `A.find`, and
  validates the actual target count and tweak list
  (`proofs/TweakableHashFunctions.eca:57-68,71-134`);
- SM-DT-TCR lets `A.pick` choose `(tw,x)` target queries and later runs `A.find`
  (`TweakableHashFunctions.eca:261-335`);
- SM-DT-DSPR and SM-DT-SPprob independently run the same oracle adversary's `pick` and `guess`, use
  its selected index, and validate the actual query list
  (`TweakableHashFunctions.eca:350-454`).

The Lean interfaces do none of that. `runCertifiedComponent` first samples a completed
`CertifiedHonestOutcome` whose marginal is the original `honestTranscriptDistribution`
(`Architecture.lean:418-441`). Only afterward, `tcrComponentProbability`,
`dsprComponentProbability`, `forsFSPprobability`, and `preComponentProbability` pass a static
`TargetPublicView` to a `ProbComp` post-processor (`Architecture.lean:486-555`). Their
`ReductionSystem` fields have no target oracle or `pick` phase (`Architecture.lean:448-476`). The
program receives all formula-indexed target outputs from an already completed original-scheme run,
selects any `Fin` index, and never produces the target-query count or distinctness trace that the
source challenger validates.

Consequently the r2 same-program repair is only syntactic: DSPR and SPprob call the same Lean
function, but that function is not an `Adv_SMDTDSPR(O)` program and did not choose its targets by
running against `O`. Likewise, the static family comes from the real `slhKeygenInternal`/signing
distribution rather than the component challenger's `dpp` and target-input sampling. An adversary's
behavior is fixed by its earlier honest execution instead of being driven by the component-world
answers.

The source concrete reductions demonstrate why this state and information flow matter. FORS
constructs the target address list and target inputs in its reduction before `find`
(`proofs/FORS_ES.ec:2243-2412`), and WOTS TCR/PRE reductions retain sampled or oracle-derived state
across `pick` and `find` (`proofs/WOTS_TW_ES.ec:2652-2859`). A stateless function of the erased
post-hoc view cannot express those named programs. The then-current design and session claims of
concrete TCR/DSPR/PRE experiments and authoritative same-program SPprob therefore overstate the
current types.

### S02-R3-003 — WOTS UD-C uses the wrong real-input distribution and an unrelated collection trace

The r2 preimage leak is fixed locally: the compiled equality for `wotsUDRealImpl` shows that it
returns `targetEval ... target.input`, not `target.input` itself
(`Architecture.lean:557-565`). The remaining semantics still differ from SM-DT-UD-C.

In the source, each real target-oracle query samples a fresh `x <$ din` and returns `f pp tw x`;
each ideal query samples `y <$ dout` (`proofs/TweakableHashFunctions.eca:483-507`). The same
reduction program has access to both the target oracle `O` and collection oracle `OC`
(`TweakableHashFunctions.eca:839-842`), and the success event compares the two tweak logs produced
during that single `A.pick` execution (`TweakableHashFunctions.eca:844-870`). The concrete WOTS
reduction interleaves those two oracles while emulating its adversary
(`proofs/WOTS_TW_ES.ec:2458-2645`).

In Lean, the real handler instead reuses a preloaded target input from the certified original
SLH transcript. It does not sample a fresh input when queried. More importantly, the complete type
of `ReductionSystem.wotsFUdC` gives the program only

```lean
UDPublicView ... → OracleComp (Fin targetCount →ₒ prims.Y) Bool
```

and no collection oracle. `WotsUDValid` compares that program's target-oracle log with
`adversaryTweaks sample.2.log` from the already-completed, separate original-scheme execution
(`Architecture.lean:567-618`). Those are not the `O` and `OC` logs of one real/ideal UD-C program.
Changing the target world cannot affect the earlier adversary run, whereas it can affect every
subsequent oracle choice in the source game.

The logged target count and `Nodup` test are genuine, and the public view no longer leaks inputs or
outputs. They do not repair the wrong real distribution or missing same-execution collection
interaction. The then-current design and session claims of a “same output-only oracle program” and
“actual ... collection-disjoint queried tweaks” are therefore not source-equivalent.

### S02-R3-004 — the standalone ITSR term is not in the post-SKG/post-MKG key-generation world

The default ITSR oracle itself now has the correct local behavior: it samples a fresh `Y` per query,
the logging layer records `(request,randomizer)`, the history recomputes `Hmsg`, and the program's
returned `(randomizer,request)` is checked for freshness and target containment
(`Architecture.lean:388-416,620-640`). This closes the original-transcript defect from r2.

The surrounding program distribution is still the wrong hybrid. `itsrComponentProbability`
samples `generateKeyPair prims` in the challenger and hands that full pair to a program whose only
oracle is ITSR (`Architecture.lean:623-640`). `generateKeyPair` calls `slhKeygenInternal`, so its
FORS and WOTS secret values and public root are derived from the real `prims.PRF` and one `SK.seed`
(`OracleSurface.lean:57-72`; `HashSig/SLHDSA/Scheme.lean:85-90`). The ITSR program has no independent
`ProbComp` sampling interface with which to replace that key material.

The pinned master term is after both preceding PRF hops. The intermediate full experiment uses
`keygen_nprf` and a random function for message keys
(`proofs/SPHINCS_PLUS.ec:2132-2178`), and the named term is
`R_ITSR_EUFCMA(R_MFORSTWESNPRFEUFCMA_EUFCMA(A))`
(`SPHINCS_PLUS.ec:4341-4347`). Inside the concrete ITSR adversary, the reduction samples `ps` and
constructs an `M_FORS_ES_NPRF` key pair itself before running the adversary
(`proofs/FORS_ES.ec:2175-2239`). The generic ITSR challenger does not supply a real full-SLH key
pair (`proofs/KeyedHashFunctions.eca:1513-1565`).

Passing a PRF-generated `GeneratedKeyPair` from outside the reduction is not a mere reordering of
those random choices: it restores precisely the secret-generation world already charged to the SKG
term and supplies a different full construction. Therefore the current third summand is standalone
but not hybrid-correct. The “after the MKG hop” language in
`docs/slhdsa/security-architecture.md:46-48,107-111` and session lines 40-42,97 omits the already
completed SKG hop and overclaims primary-source correspondence.

## R1 and r2 disposition

| earlier finding | r3 disposition |
| --- | --- |
| S02-R1-001 | **Fixed locally.** Signing entries supply `(R,request)` and explicit public Hmsg entries are excluded. The quantitative term is now separate. |
| S02-R1-002 | **Partially fixed.** Raw component scalars are gone, but the target-bearing programs and ITSR hybrid still do not denote the named games (R3-002 through R3-004). |
| S02-R1-003 | **Still blocking in a new form.** Exact positive role-indexed packages are enforced, but the honest marginal cannot supply them under the current log (R3-001), and their experiment timing is wrong (R3-002). |
| S02-R1-004 | **Fixed.** `lgw_approved` requires exactly 2, 4, or 8. |
| S02-R2-001 | **Partially fixed.** ITSR is no longer the original PRFmsg transcript, but its key-generation world is not the post-SKG/post-MKG reduction world (R3-004). |
| S02-R2-002 | **Narrow selection fix only.** Both terms call the same function and use its index, but the function is a post-hoc view processor rather than the source oracle adversary (R3-002). |
| S02-R2-003 | **Partially fixed.** No preimage is returned and count/distinctness are logged; fresh real inputs and the same-execution collection oracle remain absent (R3-003). |
| S02-R2-004 | **Partially fixed.** Role tags are now precise and package-level separation was removed, but the provider remains impossible because actual logs contain no construction events (R3-001); collection logs remain from the wrong execution (R3-003). |

## Gates that passed

- Authority pin: `/home/alh/SPHINCS/FV-SPHINCSPLUS-EC` is clean at exactly
  `a28e4c53897a4bb57b575a177225862d48f824b7`. The four inspected source hashes were
  `3bb1ce65...SPHINCS_PLUS.ec`, `67b0031d...KeyedHashFunctions.eca`,
  `ac5e354b...FORS_ES.ec`, and `1e1f5c82...TweakableHashFunctions.eca`. The 34-page repaired report
  at `/home/alh/SPHINCS/SPHINCS_EC.pdf` is 745834 bytes with SHA-256
  `d1ca5fff2e7544c3591d665cd04a2e0f7454c0a2971388911eb6f6303c026001`.
- RHS syntax: `Architecture.lean:652-683,713-727` has the two absolute PRF differences, ITSR,
  truncated DSPR-minus-SPprob, coefficient `3`, the five remaining `-C` probability terms plus UD-C
  difference, coefficient `w-2`, and all twelve roles in the exact order of
  `SPHINCS_PLUS.ec:4338-4370`. There is no birthday or additive `qS`/`qH` summand.
- Closed roles: the independent probe evaluated construction/primitive/master/target role cards to
  `8/6/12/8`. `TargetRole.constructionRole` maps bijectively by constructors, so the r2
  definitionally-equal-role counterexamples no longer compile.
- Exact formula evaluation at `slhdsaSha2_128_24`: the eight counts are respectively
  `422212465065984`, `422212439900160`, `4194304`, `285212672`, `1140850688`,
  `285212672`, `4194304`, and `4194303`. The `2^h` FORS multiplier, WOTS/XMSS sums, positivity, and
  exact-index nonemptiness match the reviewed formulas.
- Parameter and query gates: `lgw_approved` excludes one; `SigningBound` and `HashQueryBound` are
  `IsQueryBoundP` predicates on `adversary.main pk` for every public key; their one-query-zero-budget
  and pure-zero regressions compile.
- Original EUF execution coupling: `generateKeyPair` owns the public seed/root and `queryImpl`
  evaluates the original experiment's primitives with that pair. Public `AdversaryQuery` has no PRF
  or PRFmsg constructor. This pass does not cure the component-hybrid issue in R3-004.
- Local notion gates: the FIPS digest is recomputed; scheme-transcript ITSR history is signing-only;
  target outputs are challenger-computed; the two `Tl` arities remain `Vector Y k` and
  `Vector Y len`; UD public views expose neither inputs nor real outputs.
- Classical boundary: `ClassicalModel` exposes only `OracleComp`; `QROMClaim` has no constructor;
  no quantum semantics, theorem, or cast was found.
- Scope and admissions: the current changes before this r3 artifact are the four allowed modules,
  generated aggregate imports, two S02 documents, and r1/r2 artifacts. No accepted S00/S01 file or
  frozen harness changed. The new modules contain no `sorry`, `axiom`, `unsafe`, `extern`,
  `partial`, initializer, implementation override, forbidden import, or linter suppression. The
  eleven `noncomputable` declarations are probability/ENNReal experiment evaluations. The legacy
  placeholder is unchanged and its warning remains visible.

The request encoder remains a disclosed future API boundary. As in r1/r2, the current EUF event is
exact only relative to the supplied encoder, not yet a FIPS pure/pre-hash API theorem; this was not
counted as a fifth r3 finding.

## Independent command and axiom evidence

```text
git rev-parse HEAD; git status --short --branch; git diff --name-only;
git ls-files --others --exclude-standard; git diff --check
  PASS: requested branch/commit and allowed S02 scope confirmed; whitespace check passed.

git -C /home/alh/SPHINCS/FV-SPHINCSPLUS-EC rev-parse HEAD
git -C /home/alh/SPHINCS/FV-SPHINCSPLUS-EC status --short --branch
sha256sum over the four pinned source files
nl/rg over SPHINCS_PLUS.ec, KeyedHashFunctions.eca, FORS_ES.ec,
  WOTS_TW_ES.ec, OpenPRE_From_TCR_DSPR_THF.eca, and TweakableHashFunctions.eca
  PASS: clean authority pin and the master/hybrid/ITSR/target/collection programs confirmed.

lake env lean HashSig/SLHDSA/Security/Notions.lean
lake env lean HashSig/SLHDSA/Security/OracleSurface.lean
lake env lean HashSig/SLHDSA/Security/Transcript.lean
lake env lean HashSig/SLHDSA/Security/Architecture.lean
  PASS: all four modules elaborated independently with no output.

lake build HashSig
  PASS: all 2748 jobs; only the pre-existing rejected
        HashSig/SLHDSA/Security.lean:150 sorry warning was replayed.

lake env lean /tmp/S02R3IndependentProbe.lean
  PASS: role/count evaluations, exact current program signatures, no-query empty-log distribution,
        empty-log package impossibility, corrected UD output equality, standalone ITSR history, and
        the axiom audit all compiled.
```

The focused probe ran `#print axioms` on parameter restrictions, the new construction-role card,
ITSR coherence, query-bound regressions, target positivity/nonemptiness and role mapping, both
public-view erasures, collection/UD validity, SPprob, both UD worlds, standalone ITSR,
`componentTerm`, `eufAdvantage`, `repairedRHS`, `RepairedMasterStatement`, and budget independence.
Every declaration was axiom-free or depended only on the accepted `propext`, `Classical.choice`,
and `Quot.sound`; no `sorryAx` or other axiom occurred.

Source scans over the four modules found only the eleven documented `noncomputable` definitions and
no new admission/runtime mechanism. Forbidden `Extern`/`Interop` imports were absent.

## Final decision

Final verdict: **FAIL with four blocking findings and zero nonblocking findings**. R3 repairs the
surface counterexamples from r2 but does not yet define inhabitable, primary-source-equivalent
component experiments. Re-review should wait for a target distribution that the actual logged
execution can certify, in-game target-oracle reductions for TCR/DSPR/SPprob/PRE, a WOTS UD-C program
with fresh real inputs and same-execution collection access, and the correct NPRF post-hop ITSR key
world. No commit, push, or PR was created.
