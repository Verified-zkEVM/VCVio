# Tooling integration and the semantic import boundary

The importer uses the official Cryptol frontend and specializer. The parser,
renamer, typechecker, module instantiation and typed-AST serialization remain an
explicit external assumption. A transformation after that boundary produces a
candidate, whose correspondence must be proved in Lean before an implementation
certificate is reused. Typechecking a candidate is insufficient.

The recommended semantic anchor for broader imports is the documented lazy
language semantics, starting from the pinned reference account. The
[semantic survey](https://github.com/Verified-zkEVM/PolyFun/blob/main/PolyFunCryptol/docs/evaluators.md) distinguish that account
from both evaluator implementations and from SAW's translation. Known backend
differences require versioned compatibility claims; they are not automatically
changes to the canonical language model. The current partial-input theorems
remain about the existing Lean model. The source importer, native representation
theorem, external execution check and security-game replacement theorem are
separate claims.

## Implemented route

1. `cryptol-lean-export FOUNDATION MODULE ROOT...` loads and typechecks roots
   through the official Haskell library and exports their dependency closure.
2. `--specialize` additionally runs Cryptol's
   `Transform.Specialize.specializeEWhere`, returning **both** the original
   bundle and a candidate bundle. Primitive instantiations remain explicit.
3. `SourceElaboration.check bundle root` checks scope, kinds, closed constraints,
   the root schema and expression typing, then returns the canonical
   `Resolved.Term`, a scoped polynomial tree. The certificate retains the
   exact input and output equation, proved by Lean kernel reduction.
4. `ImportedSpecialization.accepted` checks the actual specializer output for
   Foundation's `sigma_256_0`. `ImportedSpecialization.correct` proves equality
   with the original import in the current partial model, including errors and
   bottom. `ImportedScalar.compiled` certifies the scalar against `ssig0` by native
   evaluation, with no proof about the lazy semantics.
5. `ImportedSpecialization.core_correct` proves agreement with VCVio's actual
   `Sha2.ssig0` for every `UInt32`. The independent `Consumer` package uses
   ordinary imports. The existing contract and probability layers remain the
   interfaces for consumer proofs.

The specializer adapter needs a deliberate restriction. Cryptol 3.6.0's
[`specializeConst`](https://github.com/GaloisInc/cryptol/blob/61dd17b0c45ddf8c5c1e952afd5e789c4dc4ec4b/src/Cryptol/Transform/Specialize.hs)
clones `DPrim` declarations, freshens their names and removes the type arguments.
For `number`, these arguments contain the literal's value: the resulting
monomorphic `Integer` declaration does not identify that value. The adapter
excludes primitives from the specializable declaration cache, using the public
lower-level specializer API. It does not infer a missing value from a fresh name
or accept the transformation on trust. A regression changes rotation 7 to 8:
the mutated candidate still typechecks, but its kernel import certificate fails.

The typed importer also accepts monomorphic lexical `where` declarations,
finite sequence literals, tuples, records and projections, closed property
guards, and single-generator comprehensions of finite or infinite length. It
recognizes a bounded primitive fragment including integer addition,
multiplication and subtraction, literals, integer indexing and finite `foldl`.
Other instantiations fail explicitly. Nine official frontend canaries have
kernel-checked import equations; their semantic tests exercise captured locals,
higher-order functions, folds, and finite observations of infinite sequences.
The external driver compares original and lowered expressions in both evaluator
modes on 36 observations. These observations are regression evidence, not a
general preservation proof.

Source types remain attached to elaborated terms until the root schema has been
checked. Tuples lower to right-associated products ending in unit; record fields
use the frontend's canonical order. Source-type equality is kernel-reducible and
has a `LawfulBEq` proof. Its equality proof supplies typed transport. Thus two
records with different labels, or a record and a tuple with the same carrier,
cannot pass application/root checking merely because their Lean carriers match.

## Whole-Foundation discovery

### Whole-module retention and checking

PolyFun owns the whole-module tooling: the exporter's `--module-bundle` mode, the
Lean decoder, scope checker, linker and module elaborator, the per-instance
diagnosis, and the census of all 135 tracked files. Its
[tooling guide](https://github.com/Verified-zkEVM/PolyFun/blob/main/PolyFunCryptol/docs/tooling.md) lists the drivers and committed outputs, and
its [Foundation status](https://github.com/Verified-zkEVM/PolyFun/blob/main/PolyFunCryptol/docs/compatibility.md) records every independent
blocker of typed elaboration for all 155 module instances. This directory keeps
only the retained utility bundle `artifacts/modules/list.json`, regenerated by
`scripts/import_imperative.py`, for the `Imperative` import below.

### Shared open modules and generated loop interfaces

The open checker registers a declaration's scheme in its source group's scope.
References are typed positions in that context; bodies are checked once, without
recursive inlining or finite monomorphization. Numeric, type, proof and value
binders use the existing scoped constructors. Local and module declarations use
ordered `Term.letE`/`Term.letRec` composition; PolyFun's `ScopedDomain.Env.fixGroup`
is used once per recursive group, before specialization. Module numeric/type parameters, assumptions and value parameters
remain explicit. Official primitive fallback edges resolve to actual named source
declarations, although the complete Reference closure does not yet elaborate.
`Declarations.denote_close` proves agreement between closing a term under these
groups and interpreting the shared environment. Correspondence with an independent
source semantics still needs a preservation proof; acceptance does not prove it.

`Constraint n v` now retains both numeric and value-type variables. Structural
class/literal constraints are admissibility predicates, not runtime dictionaries.
Closed frontend types and open constraints share the class, literal and numeric
comparison implementations. The source-to-carrier mapping is defined once in
`Reference.ValueType`; source shape remains distinct during expression checking.
Partial numeric comparisons require defined results; two undefined expressions
do not satisfy equality. Substitution and staged semantic laws cover the expanded
constraint language. Proof applications use `ConstraintEvidence.prove`: ambient
assumptions, compositional finiteness/definedness and supported numeric/class/literal
calculations produce Lean proofs. General entailment and checked coercions remain
work.
Sequence lengths and numeric instantiations still use the old total `NumExpr`
fragment: parsing a partial expression does not silently give it a total meaning.

`source module-code FILE MODULE` folds an accepted polynomial tree to candidate
Lean constructor expressions. It is an untrusted renderer. `Bridge/Imperative.lean`
imports the retained `artifacts/modules/list.json` with `cryptol_import … module`,
which renders the same bodies, declares them, and proves `Imperative.accepted`, an
exact kernel-checked elaboration equation for the module's dependency-closed bundle.
Keeping these bodies explicit avoids repeated frontend evaluation in consumer
proofs. `source module-elaborate FILE MODULE` reports typing without rendering.

`Bridge.Imperative.whileLoop` and `doWhileLoop` use the imported shared environment.
Their public equations retain suspended callback/state values, observable errors
and least-fixed-point recursion. A false condition does not demand the while
body; do-while takes one body application first. Ordinary-import tests include
an unused divergent body, an undefined initial state ignored by a constant body,
and a terminating iteration that changes the state. These are partial meanings,
not a total native loop compiler. No source-correspondence axiom or admitted
implementation is used.

The next foundational change must make type interpretation partial under valid
parameter assignments: migrate symbolic lengths and numeric applications together,
carry definedness through scheme binders and substitution, then reconstruct the
coercions justified by frontend constraints. Do not use `getD 0`, erase failed
type computations, or add a parallel syntax to bypass this gate. Aggregate and
nominal lowering must retain source shape/identity during checking before using
the existing lazy product/sum carriers. The complete five rejected modules remain
the acceptance workload; upstream-semantic preservation, native CRC correspondence
and adaptive VCVio replacement are still separate outstanding gates.

### Partial List views and native CRC

`Bridge.ListView.Represents` relates a native finite list to Foundation's
stream-and-integer representation, using the existing right-associated tuple
spine. `coreType_list` connects it to the importer's carrier. It requires the
length and exactly the in-range element observations; the unused tuple-spine
terminator is unconstrained. An empty list does not demand its stream at all.
`represents_encode`, `represents_leftTotal`, and `represents_leftUnique` prove
representation and uniqueness of the native result without equating arbitrary
unused tails. Contract transfer uses Mathlib's `Relator.LiftFun` and PolyFun's
`RelationalContract`; the embedding-based contract is a special case using the
same transfer proof. These representation laws do not yet certify Foundation's
`toList`, `map`, `fold`, or changing-instantiation recursion.

`VCVio.Algorithms.Crc` supplies a pure executable register with `BitVec` state,
byte input, reflection and final XOR. The leading generator coefficient is
implicit. `update_append` and `updateResult_append` are fully proved for all
parameters and inputs. `Result.crc` is the finalized observation; `Result.state`
is the resumable register. The independent consumer imports these laws normally.
The regression driver compares both fields against actual Foundation CRCUpdate
in normal and reference evaluation: 60 field observations over two standard
profiles and a seven-bit profile with a nonsymmetric XOR mask. These checks
exercise reflection order and empty messages as well as nonempty messages.
The missing all-input connection is imported `pmod`/`CRCUpdate` to this register
and the existing polynomial update equations. The native generator convention
does not cover Foundation's zero-polynomial lazy-field behavior; a future
comparison must state its positive-width/monic-generator domain explicitly.

### Named proof obligations

`obligations.json` is the local ledger; it is currently empty. PolyFun's scanner
reports the exact dependency graph of `sorryAx`-tainted declarations, including
internal auxiliaries and direct versus inherited admissions. The local audit
permits only named theorem admissions with an exact elaborated proposition and
digest, source, owner and reason. It rejects admitted implementations, additional
axioms, native trust, unlisted admissions and stale ledger entries. Its output
lists every declaration's transitive obligations; `no-admissions` describes
kernel debt, not language-semantic coverage.

The optional validation driver keeps its ordinary warning-failing build when
the ledger is empty. With recorded obligations, it checks the compiled report
and accepts only the exact `sorry` diagnostic at a recorded theorem's source
location. Every other warning still fails. This policy is confined to VCVio's
optional development: PolyFun's own baseline and `--check` remain strictly
zero-debt. `test_obligations.py` mutates propositions, kinds, dependencies,
warning locations and ownership metadata to test the rejection paths. It also
compiles temporary Lean fixtures and audits the real scanner output and warning
locations: a named theorem admission propagates to its client, an executable
definition remains debt-free, and an admitted definition is rejected even if
listed in the local ledger. These fixtures stay outside the library aggregates.

On VCVio main with the published PolyFun revision
`d96b2079eaa1feebf0f42aded1ff3f15b280f38e`, optional build/lint/tests/axioms pass.
The optional Bridge axiom sweep covers 487 declarations across 27 modules with no
admissions or nonstandard-axiom taint. The language model is swept by PolyFun's
suite, which covers 22,674 declarations across 577 modules with the same zero-debt
result. Pinned
external validation also passes at this pin. That covers byte-identical
regeneration of the 31-root export and the retained utility bundle, and the
Foundation bridge comparisons. PolyFun's external validation regenerates the
census, the Foundation status and the 152-observation evaluator audit. The Cryptol 3.6.0 release supplied the binary. The exporter was
built against the identified compatibility frontend, and the upstream evaluator
`51405420cb90cf9959ca4349eea0ae8b77487855` was built without FFI.

## Architecture decisions

| Concern | Canonical choice in VCVio | Reason and remaining obligation |
|---|---|---|
| Official input | `Reference.Expr` and versioned `SourceBundle` | Mirror the external AST, retaining unresolved obligations for checking. This is input data, not a second typed computation model. |
| Checked monomorphic language | `Resolved.Term` on `ScopedSignature` / `IFreeM` | Intrinsic binding, type-preserving substitution and polynomial directions already exist. Labels are checking metadata, not a new evaluator. |
| Open quantifiers and module parameters | Existing `ScopedFamily` / `Polymorphic.Term` | Numeric/type/proof stages and simultaneous recursion require this extra information. General source elaboration into it remains missing. Do not approximate higher-order parameters with data-only codecs. |
| Partial meaning | Existing lifted domains and continuous functions | Error, divergence, suspended components and partial function arguments are relevant. Document each primitive's intended meaning and any backend disagreement. |
| Native data implementation | PolyFun's `DataCertificate`, the generic `CertifiedMeaning` at Cryptol's data embedding | Native evaluation (`Resolved.dataCertificate`) certifies source directly. Finite descriptions (`Finite.Term.dataCertificate`) remain for recursion and loops, which native evaluation does not run. |
| Contracts | PolyFun's generic correspondence plus VCVio's domain adapter | `CertifiedMeaning.congr` restates a certificate against a separately written native function rather than adding a parallel transformation-contract hierarchy. |
| Execution | Existing `Control.Transition`, ITree and machine adapters | No heap evaluator was added just to obtain another model. A heap needs a measured sharing requirement and a simulation/adequacy obligation. |
| Core syntax | Existing `Expr` remains the operational/adequacy backend | It also has internal `force`; removing this carrier requires migrating those proofs and normal demand rules together. A second cosmetic polynomial wrapper would add a bridge without removing the duplicate. |

PolyFun already supplies the constant-family equivalence, renaming/substitution
laws, family reindexing, transition execution and ITree/machine bridges. The
companion's shared folds further reduce duplicate proof infrastructure. This
tranche does not need another generic carrier or contract predicate. PolyFun's
[model guide](https://github.com/Verified-zkEVM/PolyFun/blob/feat/cryptol-model/docs/guides/computation-models.md)
explains when free trees, resumptions, ITrees and dynamical machines retain
different useful information. They are useful viewpoints; importing Cryptol
does not require exposing all of them as competing VCVio APIs.

The open-PR audit on 2026-10-19 found three PolyFun drafts: [#290](https://github.com/Verified-zkEVM/PolyFun/pull/290)
at `103be8e` supplies the shared interop substrate; [#289](https://github.com/Verified-zkEVM/PolyFun/pull/289)
at `22752df` supplies independent example projects; [#308](https://github.com/Verified-zkEVM/PolyFun/pull/308)
at `d377c76` adds stateful service-machine composition. The current VCVio pin
already has every shared API needed by this tranche. None of these drafts needs
to be merged or imported wholesale to check the scalar specializer. Review the
generic #290 API before expanding the importer, use #289 to test independent
consumers, and bring #308 into scope when stateful service composition has an
actual Cryptol consumer. That keeps the dependency decision tied to a use case.

## Remaining investigation and implementation gates

The end-to-end specializer pilot is a **scalar**, not a replacement for the full
compression import. The existing SHA256 compression theorem still uses its
separate preserved-source extraction. The new typed-AST path does not yet cover
its full primitive closure, sequential/parallel comprehensions, local polymorphic
definitions and recursive groups. A source elaboration preservation theorem must
relate accepted constructors to the specified source semantics before this route
can establish general frontend correctness. A type certificate alone cannot do
that work.

The next compression gate is to elaborate the exact `Core::step` closure,
retaining dependency sharing, then replay the schedule/fold proof through that
certificate and recover the existing byte-function and adaptive-client theorems.
The next CRC gate is to elaborate `shared::CRC::Main` with its one type and seven
value parameters, connect imported `pmod` to the existing polynomial update
lemma, and prove incremental composition. The current CRC theorem is still about
transcribed equations. Module inventory success does not close either gate.

Backend compatibility requires more than agreeing on integer division. The audit
finds packed-word comparison, shift/update demand, error precedence in function
arithmetic, folds and comprehension differences. The survey classifies upstream
intent separately from observed behavior. Preserve the original Foundation theta
expression; a portability repair is a separate source artifact and proof claim.

The revised priority is whole-module import with explicit unfinished proofs,
rather than completing every proof for another narrow primitive fragment.
Import parameterized and recursive definitions before requiring specialization
or total native implementations. Use the census to measure progress over complete
dependency closures, including public properties as definitions. The
[unified tracker](https://github.com/Verified-zkEVM/VCVio/issues/879) sequences
canonical syntax, upstream reference-definition reuse, native API generation,
named proof obligations, and substantive consumers for PolyFun models.

## Related tooling and ancestry

* Cryptol's official module loader, typed AST and specializer are the active
  dependency. Its `MonoValues` pass handles internal recursive polymorphic values
  for sharing; treating its output as another checked candidate is preferable to
  implementing that optimization independently. RPC is appropriate for a
  long-lived discovery/evaluation client; the linked Haskell adapter is needed
  for the typed graph and transformation entry points used here.
* [SAW's Cryptol integration](https://galoisinc.github.io/saw-script/master/saw-user-manual/proofs-about-cryptol.html)
  translates Cryptol into SAWCore and proves properties through its own tooling.
  SAW's [design paper](https://saw.galois.com/files/saw-vstte-final.pdf) motivates
  shared symbolic terms and normalization. SAW can be a future candidate producer;
  its ordinary solver result is not automatically a Lean proof artifact. Add a
  checked relation to SAWCore/exported terms before claiming that bridge.
* [Cryptol's Coq semantics](https://github.com/GaloisInc/cryptol-semantics) and
  `:extract-coq` are direct ancestry for importing Cryptol definitions into a
  prover. That project includes cryptographic examples connected to FCF; it is
  not evidence of complete current Cryptol semantics. The existing compression
  path here used the constructor dump; the linked typed-AST route avoids writing
  another source parser.
* [Allais, Atkey, Chapman, McBride and McKinna](https://arxiv.org/abs/2001.11001)
  provide the generic scoped-syntax/semantics ancestry. PolyFun's scoped and
  parameter-changing polynomial signatures make those concerns reusable rather
  than Cryptol-specific. The key question is whether specialization and proof
  transport use those shared laws, not whether another syntax datatype can be
  presented as a polynomial.
* The certificate approach follows translation validation: an external optimizer
  proposes a term and the prover checks the relationship required by the
  consumer. This is established architecture, not a novelty claim.
  [CryptHOL](https://isa-afp.org/entries/CryptHOL.html) and
  [EasyCrypt](https://github.com/EasyCrypt/easycrypt) are relevant ancestry for probabilistic program logic and game-based
  proofs; the measure-based VCVio replacement theorem is downstream of this
  deterministic importer. Neither their existence nor differential testing
  supplies Cryptol semantic preservation.
* [CV2EC](https://bblanche.gitlabpages.inria.fr/CryptoVerif/cv2EasyCrypt/) is a useful
  example of combining existing cryptographic proof tools through an explicit
  translation boundary. Its lesson for this project is architectural: use the
  upstream tool for the task it already performs, and identify the proof claim
  crossing the boundary. It is not a Cryptol importer or a Lean certificate checker.

The distinctive experimental combination is official Cryptol candidate generation,
scoped polynomial syntax, partial-domain reasoning, native Lean implementations
and direct VCVio game replacement. This tranche demonstrates the first three
with a checked scalar and reuses the established native bridge. A claim of novel
“full verified Cryptol interop” would be premature until the remaining language,
source-preservation and whole-module gates are closed.

## Coordinated development contract

The implementation work is tracked by
[the unified roadmap (#879)](https://github.com/Verified-zkEVM/VCVio/issues/879);
its workstream table is the live
assignment and dependency queue. The semantic survey above remains the evidence
for these choices. This section specifies the intended delivery contract, not
additional implemented coverage. Work can stay on VCVio #840 and the companion
PolyFun drafts while the architecture is tested.

### Completion means several different things

The target is every module, interface and public definition in the pinned
Foundation corpus, retaining complete dependency closures and original bodies.
“Import all Foundation” is a corpus milestone, not a claim to support every
possible Cryptol program or to prove every Foundation property.

| Claim | Required evidence |
|---|---|
| Frontend coverage | The official loader exports the pinned source, parameters, schemas, properties, nominal declarations and dependency graph. |
| Structural import | Every source body is retained with stable identity and scope; unsupported forms remain explicit diagnostics or obligation-bearing syntax, never invented implementations. |
| Semantic import | Each retained constructor and primitive has the specified meaning. External implementations are explicit parameters/contracts; an unspecified parameter is reported separately from a closed semantic definition. |
| Natural Lean use | Named module interfaces, records/enums, aliases, words/sequences and public equations support an ordinary-import consumer. |
| Executable native use | A native implementation exists on a stated represented domain, with explicit totality or partial-execution conditions. Noncomputable denotation alone does not satisfy this. |
| Verified source/native comparison | Preservation and representation obligations are discharged, or the theorem is clearly conditional with a transitive report of its exact unfinished assumptions. |
| Backend compatibility | A separate versioned theorem or explicitly limited observation relates the model to normal Cryptol, reference evaluation, SAW or another backend. |
| Algorithm/security claim | Independent specification or game theorems establish the named algorithm/property. Importing a source property does not establish its truth. |

A first useful broad delivery retains real definitions and named unfinished
proofs. It need not have optimized code or complete property proofs for every
module. A `sorry` body, default result, injected bottom or language error is not
a substitute for an unsupported source definition. Unknown primitives and
foreign implementations need explicit parameters and contracts. Do not assert
an equality contradicted by a known semantic discrepancy and call it proof debt.

The optional Cryptol gate rejects all unlisted admissions. Its scoped obligation
manifest records exact declaration/proposition, source identity, reason, owning
workstream and transitive affected conclusions. Reject unlisted debt and nonstandard proof
axioms; keep PolyFun's baseline empty and core VCVio's isolation unchanged.
Proof debt is allowed in this exploratory consumer, not silently inherited by
generic infrastructure. No admission policy or baseline changes are made by
this roadmap itself.

### One source language and explicit interpretation boundaries

The planned canonical source is the existing parameter-changing polynomial
`ScopedFamily` language. It retains numeric, type, proof and value binders;
open schemas; global references; module interfaces/parameters; and simultaneous
recursive groups. Specialization is a derived operation. Recursion is interpreted
before instantiation, rather than by enumerating a finite set of instances.

`Scheme.guard` now carries open numeric and value-type constraints through one
substitution interface. Structural classes in the supported fragment are
admissibility predicates. General entailment, selector constraints and partial
type interpretation remain explicit gaps. Decide whether additional constraints
need evidence or runtime dictionaries from source semantics, rather than from
what is convenient for the target typechecker.

Keep source types and nominal identities through checking. Native carrier
equality does not justify equating different records or enums. Keep global
dependency sharing rather than expanding definitions into each call site.
Extend the official adapter, not a new source parser, for cases, nominal forms,
module linking and source positions.

Consolidate the existing source representations as consumers migrate.
`Resolved.Term` should become a closed view/embedding or a justified optimization
IR. The operational `Expr` and internal `force` require an explicit demand and
adequacy migration, not a cosmetic polynomial wrapper. `Finite.Term` has a
different possible role as a total implementation IR; compare it with directly
generated Lean definitions on the same modules before making it mandatory.
Keep one public correspondence route whichever native path a consumer uses.

The semantic anchor is documented lazy language semantics, beginning with the
pinned reference account. A known implementation disagreement is a versioned
compatibility issue. It must not silently change a primitive in isolation and
create a hybrid evaluator. The original Foundation theta source and a repaired
variant remain different artifacts.

### Work packages and integration order

The linked sections of that single issue contain concrete files, acceptance
criteria and handoffs.
Dependencies mean usable interfaces or inputs, not necessarily completion of
all proofs in a prerequisite issue.

| Package | Primary deliverable | Required inputs |
|---|---|---|
| [V1: track whole-corpus imports and explicit proof obligations](https://github.com/Verified-zkEVM/VCVio/issues/879#v1) | Whole-corpus declaration/SCC queue, provenance and explicit obligation reports | Existing inventory and validation |
| [V2: import open modules through canonical scoped syntax](https://github.com/Verified-zkEVM/VCVio/issues/879#v2) | Canonical open schemes, module environments and graph importer | V1 identities, P1 binding interfaces |
| [V3: cover nominal values, cases, and complete comprehensions](https://github.com/Verified-zkEVM/VCVio/issues/879#v3) | Nominal/base value families, cases, updates and complete comprehensions | V2 source contract, P2 semantic laws |
| [V4: link official reference definitions and primitive fallbacks](https://github.com/Verified-zkEVM/VCVio/issues/879#v4) | Official reference/fallback linking and primitive contracts | V1 provenance, V2 graph interface |
| [V5: generate natural Lean interfaces for imported modules](https://github.com/Verified-zkEVM/VCVio/issues/879#v5) | Generated native module APIs and representation transport | V2/V3 interfaces, P2 contracts |
| [V6: import complete Foundation utility modules](https://github.com/Verified-zkEVM/VCVio/issues/879#v6) | Complete List/Sort/Imperative/Enum imports and usable laws | V2–V5, without waiting for every proof |
| [V7: scale whole-module import from CRC and SHA2 to all Foundation](https://github.com/Verified-zkEVM/VCVio/issues/879#v7) | CRC and full SHA2, then every remaining Foundation module | Corpus queue and common importer/native APIs |
| [V8: execute real imported closures with resumable machine semantics](https://github.com/Verified-zkEVM/VCVio/issues/879#v8) | Actual imported closure execution and incremental state proofs | Canonical source, utilities, P3 execution laws |
| [V9: validate semantic preservation and backend compatibility explicitly](https://github.com/Verified-zkEVM/VCVio/issues/879#v9) | Source preservation, candidate validation and backend compatibility | Ledger and source/primitive contracts |
| [V10: compare imported implementations directly in VCVio](https://github.com/Verified-zkEVM/VCVio/issues/879#v10) | Direct native comparisons and adaptive VCVio game consumers | Native APIs and real algorithm imports |
| [P1: support reusable open-module binding and recursive environments](https://github.com/Verified-zkEVM/VCVio/issues/879#p1) | Shared mixed-binding/module-environment laws | Concrete V2 interface requirements |
| [P2: generalize lazy value relations and representation transport](https://github.com/Verified-zkEVM/VCVio/issues/879#p2) | Shared lazy/logical relations and representation transport | Concrete V3/V5 proof requirements |
| [P3: connect imported programs to observable incremental machines](https://github.com/Verified-zkEVM/VCVio/issues/879#p3) | Shared simulations, finite observations and incremental machines | Concrete V7/V8 workloads |
| [P4: stress public APIs with complete independent consumers](https://github.com/Verified-zkEVM/VCVio/issues/879#p4) | Independent consumer and proof-ergonomics audit | Existing APIs first; each new API as it arrives |

A practical first wave starts V1, V2/P1 interface design, V9's contract audit
and P4's public-API baseline. V6 and V10 should write desired consumer theorem
statements against actual source modules immediately. V3/V4/V5 then implement
independent families once the small central interface is agreed. The utility and
algorithm consumers integrate continuously; operational optimization and broader
backend proofs do not block structural or semantic import.

The first whole-module checkpoint is upstream `Cryptol::Reference` plus
`shared::common::utils::{List,Sort,Imperative,Enum}`. Preserve their properties
as definitions, then prove selected useful laws. List's stream/length
representation and deliberately undefined unused tails test lazy data; its
changing-instantiation recursive helper tests real open polymorphism.
A finite Lean List view needs a validity relation, not replacement of the source.

The next checkpoint is parameterized CRC and complete SHA2. CRC connects actual
imported `pmod` to the polynomial update theorem and chunk composition. SHA2
migrates the existing compression and byte/client results to the general typed
graph route. Keccak/SHA3/SHAKE, AES and remaining modular/rational/floating or
foreign families follow the census's blocker ordering. All 135 pinned files
remain in the batch report throughout; an unsupported family does not stop
unrelated modules. Native optimization and proof closure continue independently.

### What a consumer should be able to prove

For finite represented data, the desired theorem has the schematic shape

```text
∀ x, valid x →
  denote imported (encodeInput x) = success (encodeOutput (implementation x))
```

This includes successful definedness on the stated domain. A partial-correctness
statement that says nothing when the source diverges is a different claim.
Finite inputs alone do not imply that every intermediate computation is total.

For streams, use a specified finite observation and productivity/definedness
conditions. For higher-order arguments, use a logical relation respecting their
partial domains; a data-only codec is insufficient. Reuse `CorrespondsOn`,
`CertifiedMeaning`, `DataContract` and the existing VCVio adapters. Prefer
ordinary `Equiv`, standard data types and public equation lemmas over another
certificate hierarchy.

Require a separate package to state such a theorem using generated names,
records and native words, without manually unpacking right-associated products,
recreating casts, or unfolding the interpreter. Then lift that same theorem
through an actual adaptive oracle client. Randomness remains in VCVio; seeded
Cryptol random is not a probability interpretation. Functional replacement
alone establishes neither runtime bounds nor leakage equivalence.

### Computation models must earn their use

Use the same imported development to test distinct roles:

- Scoped free families retain binding and module structure; their laws should
  remove language-specific recursive proof code.
- Domains retain partial higher-order/lazy meaning and fixed points without
  requiring global termination.
- Transition systems and ITrees execute actual closures, preserve residual
  state and support finite-observation/adequacy theorems. An empty-event
  wrapper by itself is insufficient evidence of a useful execution API.
- Returning dynamical machines express incremental CRC/SHA state invariants
  and chunk composition.
- Resumptions and service composition express continuing requests once the
  relevant productivity/termination conditions are proved.
- Free oracle computations express the surrounding VCVio client/game.

PolyFun's broader indexed/coinductive/continuation audit remains in
[issue #309](https://github.com/Verified-zkEVM/PolyFun/issues/309).
Do not force Cryptol through every model. For each proposed bridge state whether
it preserves typing, full partial meaning, finite observations, strong/weak
behavior, retained state or resource observations. Silent divergence cannot be
discarded to fit a resumption interface. Weak equivalence does not preserve a
clock. Core Lean/CSLib/Mathlib carriers and laws take precedence when they fit.

Measure graph size, generated term size, import/elaboration time, peak memory
and runtime on complete workloads. Also record repeated proof patterns, manual
casts and reliance on private definitions. Consider a heap/sharing evaluator
only after these measurements identify duplicated work; reuse official
`MonoValues` as a candidate transformation where appropriate. A new runtime
needs a simulation and its own semantics, not only faster test results.

### Agent handoff and validation

Use one worktree per agent and one integrator for the central source interface,
generated module naming and committed dependency pins. V1 owns corpus/obligation
formats, V2 owns the central typed interface, V4 owns the linked Haskell adapter,
and V5 owns generated public API conventions. Other agents add consumers or
separate constructor/primitive modules, agreeing shared-file edits first.
Record interface decisions and blockers in the owning workstream before expanding
large proofs. Keep workstream status in the unified issue; owning guides describe the
resulting contracts.

Every handoff should provide its commit, exact companion pins, public API,
acceptance consumer, validation results, removed duplication, outstanding proof
obligations and changed semantic assumptions. Publish an immutable PolyFun
revision for an integrated checkpoint. Use explicit local overrides while
iterating; never replace Lake's Git package checkout with a symlink, commit a
local path manifest, or combine unrelated drafts merely to obtain one theorem.

The current drafts have distinct owners: PolyFun #290 for generic scoped
interop, #289 for optional independent applications, #308 for service machines;
VCVio #840 for the Cryptol consumer. None must merge before exploration can
continue. Prefer extracting a shared prerequisite when it is independently
useful, fully proved and validated through its consumers. The larger split and
merge sequence can wait.

Validation follows existing drivers. Changed generic code requires PolyFun's
lint/test/zero-debt axiom checks and ordinary-import consumers. Cryptol changes
require optional build/lint/test/obligation checks; exporter/artifact changes
also require pinned regeneration and external observations. A full corpus report
must survive partial failure and report progress honestly. Tests diagnose
regressions; semantic preservation and implementation equality are proof claims.

## Ordered module and constraint checkpoint

The typed module environment now follows the linker's declaration groups.
`Declarations` is an indexed assembly telescope over the existing polynomial
terms: it records body contexts and names, closes exports with `letE`/`letRec`,
and has a proved agreement with shared environment interpretation and block
composition. It does not introduce another expression language or a new
computation model. PolyFun's existing scoped-domain fixed-point API suffices;
its pin is unchanged.

Proof search returns entailment evidence. Whole-module materialization now
records typed contexts and supplies explicit scheme/constraint arguments,
because Lean cannot generally invert substitution to infer them. Generated
constraint proofs are replayed in the kernel. The regression compiles every
body of common/properties and Ring::Primitive::Functor, not just one selected
export. Internal replay runs in PolyFun's own tests; ordinary consumers here use the
proved public bridge interface.

Partial type evaluation has substitution and monotonicity proofs and is used
by the constraint solver. The larger canonical `NumericExpr` migration remains
open; no undefined numeric operation is given a default value. PolyFun's
[Foundation status](https://github.com/Verified-zkEVM/PolyFun/blob/main/PolyFunCryptol/docs/compatibility.md) distinguishes this preparation from
the outstanding open-scheme/domain migration and records the current whole-corpus
counts.
