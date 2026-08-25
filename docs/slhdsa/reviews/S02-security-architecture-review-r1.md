# S02 independent security-architecture review r1

Verdict: **FAIL**

Blocking findings: **4**
Nonblocking findings: **0**

Reviewer: fresh independent S02 reviewer; not the S02 implementer.
Review date: 2026-08-25.
Reviewed tree: VCVio commit `c5d6cb03d11126e6290bec58ef8824f36fc3a73b` on branch
`codex/sphincsplus-formalization`, plus the uncommitted S02 worktree.

Independence and write-scope statement: I reviewed from the pinned sources, current types, and
executable probes rather than accepting the session narrative. Read-only checks and `/tmp` Lean
probes were the only actions before this verdict. This file is my only repository edit. I did not
alter the Lean implementation, `HashSig.lean`, the accepted S00/S01 infrastructure or harness, the
rejected legacy `HashSig/SLHDSA/Security.lean`, or any other documentation.

## Decision summary

The S02 surface has several sound pieces: the displayed RHS has the authoritative twelve roles in
the correct order and the visible coefficients are correct; there is no birthday or additive
`qS`/`qH` scalar; the query bounds are predicates on actual adversary computations; generated-key
execution couples the public seed/root; public and internal query languages are distinct; digest
targets are recomputed; target batches require nonemptiness and distinct tweaks; the two `Tl`
arities are separate; the target-count formulas and positivity proofs compute correctly; and the
surface is explicitly classical. The build succeeds, the role cards evaluate to `6/12/8`, and the
completed load-bearing declarations use only the accepted standard Lean axioms.

Those successes do not establish the requested architecture. The authoritative ITSR target history
is replaced by a different public-`Hmsg` history. The master RHS is fed by arbitrary bounded scalars
rather than the named game advantages. The positive count and distinct-batch interfaces are not
connected to each other, a transcript, or any reduction. Finally, the proposed parameter context
omits an explicit hypothesis of the pinned theorem. These are type-level counterexamples, not
missing proofs of an otherwise adequate statement. S02 cannot be accepted in this revision.

## Blocking findings

### S02-R1-001 — ITSR history is taken from explicit adversarial `Hmsg` calls, not honest signing requests

The then-current `hmsgHistory` definition in `HashSig/SLHDSA/Security/Transcript.lean` constructs the history only from `.hmsg`
entries and drops every other query, including `.sign`. The honest experiment logs signing as one
outer event (`Transcript.lean:118-129`), so the signer's internal `Hmsg` evaluation never creates a
`.hmsg` entry. A compiled probe establishes the consequence directly:

```lean
example {p : Params} {prims : Primitives p} (keys : GeneratedKeyPair prims)
    (encode : MessageInput → List Byte) (request : MessageInput) (sig : Signature prims) :
    hmsgHistory keys encode [⟨.sign request, sig⟩] = [] := rfl
```

This is not the authoritative ITSR experiment. The default ITSR oracle samples a key, records the
`(key,input)` pair, and returns that key at
`/home/alh/SPHINCS/FV-SPHINCSPLUS-EC/proofs/KeyedHashFunctions.eca:1486-1505`. The concrete
FORS reduction invokes that oracle from its signing oracle at
`/home/alh/SPHINCS/FV-SPHINCSPLUS-EC/proofs/FORS_ES.ec:2188-2212`; its proof invariant equates the
ITSR targets with the zipped signing message keys and signing requests at `FORS_ES.ec:3853-3867`.
The repaired report makes the same point on page 16: the target union comes from key/message pairs
for issued signature queries.

`forgeryITSRRecord` correctly takes `R` from the forged signature, and `ITSRBreak` correctly asks
that `(R,request)` be fresh, but those facts do not repair the wrong history. Conversely, an explicit
public `.hmsg` query chosen by the adversary is currently admitted to the target history even though
it is not an honest signing target. Therefore `TranscriptITSRBreak` at `Transcript.lean:106-111`
does not denote the ITSR term at `SPHINCS_PLUS.ec:4347`.

The prose overclaims this boundary at `docs/slhdsa/security-architecture.md:86-95` and
`docs/slhdsa/sessions/S02-security-architecture.md:39-40`. The later caveat that signing internals
are not exposed (`security-architecture.md:97-100`) describes the defect but does not discharge the
S02 ITSR deliverable. The log already contains the signing response and hence its `R`; the honest
`(R,request)` history must be projected from `.sign` entries (or from a semantically equivalent
refined trace), not from public `.hmsg` queries.

### S02-R1-002 — `ReductionSystem` permits arbitrary scalars and does not encode the twelve named games

`HashSig/SLHDSA/Security/Architecture.lean:169-175` gives each role an arbitrary type, a constructor
from `A`, and an arbitrary `ENNReal` named `probability`, constrained only to be at most one. It has
no role-specific game type, experiment, public-key/seed provenance, encoder, transcript, target
batch, collection-separation condition, or correspondence to the predicates in `Notions.lean`.
The constructor is syntactically a function of `A`, but it can ignore `A`.

This is executable, not hypothetical. Both of the following systems elaborate: every reduction is
`Unit`, every constructor ignores `A`, and all component values can independently be zero or one.

```lean
def zeroReductionSystem {p : Params} (prims : Primitives p) : ReductionSystem prims where
  Reduction := fun _ => Unit
  construct := fun _ _ => ()
  probability := fun _ _ => 0
  probability_le_one := by simp
  forsFSPprob := fun _ => 0
  forsFSPprob_le_one := by simp

def oneReductionSystem {p : Params} (prims : Primitives p) : ReductionSystem prims where
  Reduction := fun _ => Unit
  construct := fun _ _ => ()
  probability := fun _ _ => 1
  probability_le_one := by simp
  forsFSPprob := fun _ => 0
  forsFSPprob_le_one := by simp
```

`componentTerm` at `Architecture.lean:178-185` only gives DSPR special treatment. In particular,
the pinned SKG and MKG terms are absolute differences of two PRF experiment probabilities
(`SPHINCS_PLUS.ec:4341-4345`), and WOTS UD-C is another absolute difference
(`SPHINCS_PLUS.ec:4360-4362`); the Lean RHS supplies one arbitrary `probability` scalar for each.
The TCR, PRE, DSPR, UD, ITSR, and collection predicates declared in `Notions.lean` are not referenced
by `Architecture.lean` at all. The component probability fields can also conceal an unrelated public
seed because their type is not coupled to `GeneratedKeyPair`, `honestTranscriptDistribution`, or the
same `encode` used on the LHS.

Thus the correct role names and coefficient syntax at `Architecture.lean:200-214` do not make these
the authoritative twelve terms, and fixing the reduction system before the universal adversary
quantifier does not prevent scalar slack. The claims at
`docs/slhdsa/security-architecture.md:44-47,60-71,152-154` and
`docs/slhdsa/sessions/S02-security-architecture.md:45-46,61-62` exceed what the types enforce. The
RHS needs role-indexed concrete advantage definitions and reduction constructors whose result types
force the relevant game, key/seed, encoder, transcript, target, and collection obligations.

### S02-R1-003 — exact counts and transcript provenance are disconnected from component targets

The formulas in `HashSig/SLHDSA/Security/Architecture.lean:80-104` are correct, and
`targetCount_pos` proves their positivity. But `positiveTargetCount` is never consumed by a game or
reduction. `DistinctTargetBatch` at `Notions.lean:172-175` has no exact-length or formula field, and
the component predicates accept any nonempty distinct-tweak list. A compiled singleton batch has
length one while the named target count for FORS `F` is `422212465065984`.

`honestTranscriptMap` at `Transcript.lean:131-138` also accepts an arbitrary extractor. Preventing a
second `ProbComp` argument does not establish provenance: `extract` may ignore its transcript and
return any constant fabricated batch. No field requires that a batch be the construction targets in
the logged key/signing execution, that its length equal `targetCount p role`, or that its tweaks and
inputs correspond to the relevant `F`, `H`, or `Tl` calls. `ReductionSystem` does not mention
`honestTranscriptMap`, `positiveTargetCount`, or `DistinctTargetBatch`.

Consequently the statements that callers cannot substitute unrelated targets and that the eight
games use the exact counts are false at `docs/slhdsa/security-architecture.md:69-71,126-148` and
`docs/slhdsa/sessions/S02-security-architecture.md:35,39,52-59`. The remaining-obligation admissions
at `security-architecture.md:156-159` and `S02-security-architecture.md:107-110` confirm that target
provenance and concrete reductions have not been implemented; they do not satisfy the S02 gate in
`docs/slhdsa/plan.md:64-70`.

Each target-bearing role needs a dependent honest-transcript-derived challenge package carrying the
exact formula equality, nonemptiness, distinct tweaks, the appropriate `Tl` arity, recomputed output,
and any collection/address separation required by its concrete game. The master terms must consume
those packages.

### S02-R1-004 — the context omits the authoritative `log2_w ∈ {2,4,8}` condition

The pinned EasyCrypt development requires
`log2_w = 2 \/ log2_w = 4 \/ log2_w = 8` at
`/home/alh/SPHINCS/FV-SPHINCSPLUS-EC/proofs/SPHINCS_PLUS.ec:39-41`. In contrast,
`ParameterConditions` at `HashSig/SLHDSA/Security/Notions.lean:51-59` requires only `0 < p.lgw`.
The following invalid-for-the-source context elaborates:

```lean
def invalidLogWParams : Params :=
  { n := 1, h := 1, d := 1, hp := 1, a := 1, k := 1, lgw := 1 }

example : ParameterConditions invalidLogWParams := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, ?_, by decide, rfl⟩
  decide

example : ¬ (invalidLogWParams.lgw = 2 ∨ invalidLogWParams.lgw = 4 ∨
    invalidLogWParams.lgw = 8) := by decide
```

This affects the sourced WOTS domain and the `(w-2)` coefficient, not merely target positivity:
`lgw = 1` gives `w = 2` and a zero UD-C coefficient, while the authority restricts `w` to
`4`, `16`, or `256`. Because `ClassicalSecurityContext.conditions` is the only parameter hypothesis
of `RepairedMasterStatement`, the proposed statement can be instantiated outside the theorem it is
claimed to model. Add the exact allowed-log condition (or an equivalent reviewed validity type) to
the load-bearing context.

## Gates that passed

- Authority pin: `/home/alh/SPHINCS/FV-SPHINCSPLUS-EC` is exactly
  `a28e4c53897a4bb57b575a177225862d48f824b7`; the repaired report has 34 pages and the cited proof
  graph/master-theorem discussion is present.
- RHS syntax: `Architecture.lean:203-214` has the exact twelve roles in authoritative order, with
  `max(0,DSPR-SPprob)`, coefficient `3`, coefficient `w-2`, and no birthday or additive budget term.
- Counts: at `slhdsaSha2_128_24`, the eight values evaluate respectively to
  `422212465065984`, `422212439900160`, `4194304`, `285212672`, `1140850688`,
  `285212672`, `4194304`, and `4194303`. These agree with the stated formulas.
- Role cards: `Fintype.card PrimitiveRole = 6`, `Fintype.card MasterTermRole = 12`, and
  `Fintype.card TargetRole = 8` all compile and evaluate as stated.
- Query budgets: `SigningBound` and `HashQueryBound` use `IsQueryBoundP` on
  `adversary.main pk`; the one-query zero-budget rejections and pure-zero lemmas compile.
- Oracle separation and current execution coupling: `AdversaryQuery` cannot express `PRF` or
  `PRFmsg`; `generateKeyPair` owns key generation; and `queryImpl` uses the generated public
  seed/root. This pass does not cure the opaque component-reduction boundary in S02-R1-002.
- Digest/predicate surface: the digest is actually recomputed through `prims.Hmsg`; `digestIndex`
  maps digest regions to tree/leaf/FORS indices; tweak targets store no caller output; batches are
  nonempty with pairwise distinct tweaks; and FORS/WOTS `Tl` queries use `Vector` lengths `k`/`len`.
- Classical boundary: `ClassicalModel` exposes only the `OracleComp` marker and `QROMClaim` has no
  constructor. No QROM cast or theorem was found.
- Scope and admissions: the S02 source contains no new `sorry`, `axiom`, `unsafe`, `extern`,
  `partial`, initializer, implementation override, or linter suppression. The three
  `noncomputable` definitions are confined to component/RHS/probability values. No accepted S00/S01
  file was modified. The legacy placeholder remains untouched and its global findings are not
  claimed closed (`security-architecture.md:161-162`; session lines 107-111).

The external `encode : MessageInput → List Byte` remains an explicitly deferred API boundary. The
current EUF probability is exact relative to that supplied encoder, not yet a FIPS pure/pre-hash API
claim; an injective, domain-separated encoding remains necessary in the later API session. This
disclosed boundary is not counted as an additional r1 finding.

## Independent command evidence

```text
git status --short --branch; git rev-parse HEAD; git diff -- HashSig.lean
  PASS: branch/commit confirmed; pre-review changes confined to the four S02 modules, two S02 docs,
        and generated aggregate imports.

git -C /home/alh/SPHINCS/FV-SPHINCSPLUS-EC rev-parse HEAD
sed -n '4338,4370p' .../proofs/SPHINCS_PLUS.ec
nl/sed/rg over SPHINCS_PLUS.ec, FORS_ES.ec, KeyedHashFunctions.eca, and SPHINCS_EC.pdf
  PASS: authority pin, twelve-term RHS, WOTS restriction, ITSR game, and signing-history invariant
        independently confirmed.

lake build HashSig
  PASS: 2748 jobs. The only warning is the pre-existing rejected
        HashSig/SLHDSA/Security.lean:150 declaration using sorry.

lake env lean /tmp/S02IndependentAxioms.lean
  PASS: role/count evaluations and the ITSR/count/reduction/log2_w counterexamples above elaborate.
```

The same Lean probe ran `#print axioms` on `PositiveTargetCount.value_ne_zero`,
`PositiveTargetCount.not_exists_value_eq_zero`, `hmsgHistory_coherent`,
`forgeryITSRRecord_coherent`, all six query-bound regression lemmas, all three role-card theorems,
`xmssTreeCount_pos`, `wotsInstanceCount_pos`, `targetCount_pos`,
`positiveTargetCount_value`, and `repairedRHS_budget_independent`. Every result was either axiom-free
or a subset of exactly `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` or other axiom
occurred.

Source-token scans over the four S02 modules found no forbidden admission or runtime mechanism, and
`git diff --check` passed.

## Final decision

Final verdict: **FAIL with four blocking findings**. The implementation may serve as an exploratory
surface, but it is not yet the S02 security architecture required by the accepted plan and pinned
proof. A re-review should begin only after the honest signing-derived ITSR history, role-specific
game/reduction advantages, transcript-proven exact target packages, and exact WOTS parameter
hypothesis are enforced by the load-bearing types and the overclaiming documentation is corrected.
