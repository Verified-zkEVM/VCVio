# B01 upstream architecture and parameter boundary integration

Status: implementation complete; fresh independent boundary review required before push.

Date: 2026-08-31
Branch: `codex/sphincsplus-formalization`
Accepted predecessor: `ca84e4f18610ba40dadd44466cd987507a199c24` (S04 r1 review committed;
the reviewed S04 repair is `00f1416ea9b8e0eb4cabd1fe28c7029beef56c34`).

## Purpose and exact inputs

This is a compatibility boundary, not a successor construction session. It reconciles the accepted
S00--S04 work with two concurrent upstream lines while preserving their histories:

- upstream main `a9dd3bd2895d2ca8bbe02af480c1df7c3be64e24`, merged normally as
  `15a26d7b`; and
- PR #593 exact head `0caf09ca831ba0686db549b596ddfeb121de69ac`, merged normally as
  `07e625f9` and retained as the merge's second parent.

There was no rebase, squash, or force push. The integration candidate remains unpushed until a
fresh reviewer accepts its exact head. No independent-review artifact or verdict is authored here.

## Resulting ownership boundary

Upstream main is canonical for Lean 4.33.1 and the `CorePrimitives`, `AdrsKey`, `Thash`,
`PublicHash`, and oracle-parametric WOTS/XMSS/FORS/hypertree/Scheme architecture. `ByteLaws` remains
the accepted S04 byte-coherence property, now attached to `CorePrimitives`. The isolated S02
security architecture is retained and explicitly parameterized over upstream `PublicKeyCore` and
`SecretKeyCore`.

PR #593 is canonical for raw `Params.Valid`, proof-carrying `ValidatedParams`, the twelve-member
`FipsParameterSet`, and the deliberately smaller `LimitedParameterSet`. The integration does not
retain the former approval-coupled duplicate `ParameterSet`/`Valid` model. Instead,
`HashSig/SLHDSA/FipsParams.lean` supplies only compatibility facts: hash family/category,
component-size and derived-width equalities, enumeration length, and family-aware lookup. The S03
codecs and S04 concrete dispatcher/tests consume `FipsParameterSet` directly.

The pure SHA2/SHAKE implementation and its vector provenance are unchanged cryptographically.
`Concrete/FIPS.lean` adapts those functions to upstream's one variable-arity `Thash`, canonical
22-byte SHA2 or 32-byte SHAKE address keys, and new primitive fields. Checked SHA2 public helpers
continue to reject non-compressible structural addresses; the total abstraction's address-key
projection fails closed. The reduced SHA2 128/24 and C13 KATs remain regressions, not FIPS/ACVP
conformance claims.

Upstream's construction code replaces the former aggregate deferred `sorry` theorem in the
HashSig root. Accordingly, the compiled policy now observes no `sorryAx` in HashSig. Under Lean
4.33.1/upstream recursion it pins five exact generated `_unsafe_rec` helpers with their safe
parents, rather than S04's seven Lean 4.32.2 helpers; the semantic rejection policy is not relaxed.

No S05 WOTS+ feature or proof was added. WOTS changes in this boundary are only those inherited
from upstream main plus compatibility needed to compile and test the accepted work.

## Concurrent work reserved for later sessions

The following exact heads were inspected for ownership only and were not merged:

- PR #594 `c0930e49f74580fc8c0c22fbbffd8496df38972a`: final-validity tweakable-hash games, to be
  consumed by S11+ security work;
- PR #595 `be823fbb6745e95412efe2bf49e0e46055953413`: digest and hypertree positions, to be
  reconciled by S08/S09; and
- PR #596 `7068fd993e35748822d07bba922fe70fe2953cd9`: DSPR, OpenPRE, UD-C, and ITSR games, to be
  consumed by S11--S16 in coordination with #594.

S05 must not duplicate these deliverables. Their future merge must repeat this exact-head,
history-preserving compatibility and independent-review discipline.

## Validation evidence

The implementation handoff includes:

- warning-free `lake build HashSig HashSigTest` under Lean 4.33.1;
- S02, S03, and S04 inventory/axiom probes;
- the all-twelve S03 codec executable, S04 primitive/vector executable, reduced SHA2 128/24 KAT,
  and C13 KAT;
- the exact compiled `PolicyAudit`, including negative fixtures, five-helper parent checks,
  initializer/extern/runtime surfaces, and exact standard axiom union;
- generated HashSig umbrella, Extern/Interop/complexity-backend isolation, and axiom-sweep gates;
- repository root builds needed to replace stale pre-4.33 artifacts;
- docs-only and full SLH-DSA validation, report rendering, and diff/source hygiene.

Native-backend stub warnings are expected when optional git submodules are absent and do not affect
these pure Lean paths. The exact command transcript and any environmental warnings must be replayed
by the independent reviewer rather than inferred from this record.

## Reviewer handoff

Review the exact unpushed integration head containing this record and its implementation payload.
Verify both merge parentages, the absence of history rewriting, the canonical ownership boundary,
all changed compatibility declarations, concrete address/hash grammar, S02 core typing, and the
complete gate set above. Confirm separately that PRs #594--#596 are absent and reserved as stated.
Any finding reopens B01; only a fresh zero-finding review may authorize the push and S05 launch.
