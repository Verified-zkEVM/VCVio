# R0a: selected signature and semantic baseline

This baseline freezes 77 selected contracts and the semantic dependency closure of
11 anchor groups. It is an initial regression gate. It does not establish the later
R0b readable semantic equations, new implementation equivalence, or P5 theorem recovery.
No original proof body delegates to these test declarations.

Run from the repository root:

```sh
python3 scripts/check-slh-dsa-r0.py --report-dir /tmp/slh-dsa-r0-check
python3 scripts/tests/test_slh_dsa_r0.py --report-dir /tmp/slh-dsa-r0-controls
```

Use fresh report directories outside the checkout. The first command builds the test
imports, then **freshly elaborates all four witness source modules** with
`-DautoImplicit=false`, even when Lake artifacts are warm. Lean's JSON reads are not
tracked Lake dependencies; `lake build HashSigTest` alone is insufficient to rerun
these guards. R0a is an explicit validation command, pending normal CI enforcement
in R0b. Global compiler attributes and executable behavior are not frozen by the kernel
syntax digests; their explicit evaluation and runtime bindings also belong to R0b.
The controls temporarily mutate only the new literal JSON artifact, restore
its exact bytes, and check that the documented verifier and fresh Lean elaboration
reject the mutation. Run the commands sequentially without concurrent source edits.

`kernel-types.json` stores a backward-referenced DAG of closed kernel expressions.
Each witness uses its artifact's type, universe parameters and declaration kind;
the selected source constant supplies only the witness value. The ordinary checked
Lean declaration API validates that value. The 75 theorem witnesses and two definition
witnesses cover exactly the 77 declarations in the original strength inventory.
`schemas.md` provides readable renderings; it is not elaborated as an expected type.

The 1,242 semantic records include types, bodies of definitions (including Prop-valued
definitions), bodies of opaque declarations when available, recursor rules, constructor
and inductive metadata, universe parameters, ownership, dependency edges and axiom sets.
Theorem proof terms are omitted; their types and transitive axiom sets are retained.
Expression metadata annotations are stripped. Definitional syntax, binder names and
reducibility metadata remain significant, so this gate deliberately rejects harmless
representation changes as well as weakening. Such changes require separately reviewed
recovery evidence; refreshing the baseline is not a passing check.

`semantic-fingerprints.tsv` contains declaration name, owning module, kind, type digest,
body digest and metadata digest. Digests use UTF-8 canonical JSON with sorted object
keys and comma/colon separators. The full capture is reproducible by the generated
external driver; its initial digest is recorded in `baseline.json`. It remains an
external research artifact, rather than a committed expression dump. Every one of the
509 external boundary references resolves to the exact toolchain or one uniquely
identified locked dependency package. Repository-owned boundary escapes fail closed.
Unavailable local implementations presented as axioms also fail closed; `import all`
is required when inspecting a non-exposed imported opaque implementation.

The verifier binds the manifest, all eleven clean dependency revisions, toolchain text
and the actual commit-bearing `lean --version` output. It brackets every acceptance
input and evaluator query with source/dependency snapshots. Source snapshots distinguish
missing files, regular bytes and modes, symlink targets, index modes and blobs, and
present gitlink revisions/status. Unrelated additive source and a later Git head are
allowed; any protected semantic change fails. The original base revision and tree are
recorded for reproduction. These checks do not authenticate an independently changed
verifier or an intentionally replaced expected baseline; review and commit provenance
remain necessary.

The focused controls compile independent environments with the same qualified names.
They detect dropping verifier cost behind an unchanged anchor, changing pair freshness
behind an unchanged Prop-valued type, adding a theorem premise, changing constructor
metadata, and changing a genuinely imported non-exposed opaque body. Positive repeated
capture is stable. This tests semantic fingerprinting, rather than comparing source
filenames or unrelated provenance hashes.


## Oracle-index universe compatibility

The guard accepts either all four original query-wrapper level interfaces, or their exact
index-independent interfaces specified by `index-universe-compat.json`. The latter mode
specializes `withAddCost` to index zero and the three trace/cost wrappers to the original
input/index diagonal. Seven named constant occurrences are checked at fixed syntax paths;
the added index must equal zero or the retained input level as specified. Unknown, mixed,
missing, moved or additional protocol occurrences fail closed. Only those four parameter
maps and seven checked slots are converted before the unchanged raw fingerprint comparison.
No term reduction, level normalization or lambda-name quotient is used. The sidecar's reviewed
SHA256 is pinned in the checker and read inside its before/after source frame.

The 77 kernel witnesses run freshly before this compatibility check. The original literal
DAG, 1242-record fingerprint table, 509-name pinned boundary and semantic roots remain
unchanged. The ordinary `signing_view_tests` executable also executes a Type1-indexed mixed
uniform/Boolean world with small messages, signatures, replies and noncommutative costs.
Kernel clients retain the old explicit universe applications and quantify independent oracle
and runtime-carrier universes. Compiled callers must be rebuilt because constant universe
arity changes; source universe parameter positions retain their original meanings.

This finite calling-convention recovery does not authorize changing protected algorithm
bodies or security premises. Future body delegation still requires a separately reviewed
recovery/evidence evolution; refreshing the frozen expected fingerprints is not acceptance.
