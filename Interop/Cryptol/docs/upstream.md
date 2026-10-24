# Dependency and source provenance

PolyFun's [evaluator audit](https://github.com/Verified-zkEVM/PolyFun/blob/main/PolyFunCryptol/docs/evaluators.md) records the current production/reference
decision, exact upstream issue #2060, related demand discussions and the
Foundation theta consequence. Generic interop work belongs in PolyFun #290;
Cryptol semantics, checked source specialization and Foundation/core
correspondences belong in VCVio #840.


The optional [Cryptol model](../README.md) pins the published PolyFun companion
at `d96b2079eaa1feebf0f42aded1ff3f15b280f38e`, the head of
[PR 366](https://github.com/Verified-zkEVM/PolyFun/pull/366). The stack hosts the
language model as `PolyFunCryptol` (#356) above the generic substrate PRs #352–#355. The shared toolchain
is Lean `v4.35.0`, Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`, and CSLib
`5b56df99362532c46e1175381fbbdd755bd56030`. Exact weakest preconditions are
exercised for finite executions; they are not a substitute for domain-theoretic
adequacy of recursion.

The optional-library organization and `ITree.Execution` adapter reuse the
design from [PolyFun PR 289](https://github.com/Verified-zkEVM/PolyFun/pull/289),
head `a8eff621945e77f1a16f86dfef7a4b5d938b15e9`. The adapter imports its handler
sum dependency explicitly on the local base.

The CSLib fork campaign at `2396178121c08eb18c8264daff87f100975cb70d` is a
design and ownership reference, not an additional imported library. Its
`PFunctor.Resumption` and several foundation names overlap local definitions.
Repinning to the whole campaign without migrating those owners would produce
collisions and pull application-specific semantics into the wrong layer.

| Fork-facing work | Relevance and ownership decision |
|---|---|
| [1: full campaign](https://github.com/dtumad/cslib/pull/1) | Inventory of foundations, machine encodings, and crypto applications; retain the pinned public CSLib as the dependency. |
| [2: free interoperation](https://github.com/dtumad/cslib/pull/2) | Compare with public 1086; the syntax boundary uses existing `IPFunctor.IFreeM`, not a second free carrier. |
| [3: possible outputs](https://github.com/dtumad/cslib/pull/3) | Compare with 1087; useful for effectful extensions, but does not characterize lazy divergence. |
| [4: transformer/state laws](https://github.com/dtumad/cslib/pull/4) | Reusable interpreter infrastructure; current call-by-name machine uses explicit typed state. |
| [5: resumptions](https://github.com/dtumad/cslib/pull/5) | Direct overlap with 1088 and local resumption ownership; add continuous interpretations to the local carrier. |
| [6: exact WP](https://github.com/dtumad/cslib/pull/6), [7: chosen free WP](https://github.com/dtumad/cslib/pull/7) | Use the local v4.35 exact-WP and free-program APIs through their public modules; keep the Std.WP quarantine. |
| [8: measure semantics](https://github.com/dtumad/cslib/pull/8) | Increasing approximations are relevant, but measure algebras are not the value CPO semantics of a lazy language. |
| [9: iteration and fair coins](https://github.com/dtumad/cslib/pull/9) | Guarded execution is relevant; sampler/termination/probability claims require a separate downstream interpretation. |
| [10: ElGamal](https://github.com/dtumad/cslib/pull/10), [11: asymptotic ElGamal](https://github.com/dtumad/cslib/pull/11) | Potential downstream consumers of verified finite descriptions and resource proofs; no security claim follows from evaluator adequacy. |
| [12: identification](https://github.com/dtumad/cslib/pull/12), [13: forking](https://github.com/dtumad/cslib/pull/13), [14: random oracles](https://github.com/dtumad/cslib/pull/14), [15: Schnorr signatures](https://github.com/dtumad/cslib/pull/15) | Keep crypto experiments, replay probabilities, oracle semantics, and security reductions in VCVio. |

The corresponding public foundation PRs have these integration boundaries:

| Public CSLib work | Audited head | Follow-up at a coordinated pin upgrade |
|---|---|---|
| [1052: folds and W equivalence](https://github.com/leanprover/cslib/pull/1052) | `cf850c792bc80d44ca315de3dfbcb85f9ef5c0d8` | Retain upstream carrier ownership; remove staging folds when their required equations are in the pin. |
| [1086: free representations](https://github.com/leanprover/cslib/pull/1086) | `8bc34b1277a4bc17216c7d225e108aadd1b54070` | Transport handlers and folds through the reviewed equivalences. |
| [1087: support and attachment](https://github.com/leanprover/cslib/pull/1087) | `4d38656e7a187913d36455a721b9b34cad6fd7d8` | Reconcile support/attachment APIs; preserve their distinction from partial lazy values. |
| [1088: resumptions](https://github.com/leanprover/cslib/pull/1088) | `316d26113c4eab0acf1d3888a3d63340f387b968` | Migrate the resumption owner and recheck constructors, lens transport, truncation, and continuous-algebra theorems. |
| [1089: measure semantics](https://github.com/leanprover/cslib/pull/1089) | `2f373a69658b9aaccc5a81a5725a05b66f54ea75` | Compare approximation APIs after 1088; keep probability-specific conclusions downstream. |

The actual missing generic substrate at these pins is continuous currying,
least-fixed-point continuity/fusion/induction, admissible predicates, and
omega-CPOs for discrete values, disjoint sums, and bottom lifting. Continuous
function packaging, fixed-predicate conditionals and discrete-map continuity
are shared proof tools for primitive interpretation. These are
staged in `ToCslib/Order/` over Mathlib's existing `OmegaCompletePartialOrder`;
there is no new competing CPO class. Generic lifted results live in
`PolyFun/Control/Domain/Result.lean`, and tree interpretations live beside the
existing resumption and ITree APIs. At upstreaming time, order-only material
is also a candidate for Mathlib. Remove superseded local instances before
importing an upstream owner; re-run the model's ordinary-import and axiom gates.

The Foundation bridge consumer targets
[VCVio PR 821](https://github.com/Verified-zkEVM/VCVio/pull/821), head
`53e93b7679cc222c26ad1027779e4840a4262a93`, with these same v4.35 pins.
VCVio #840 includes that head and main `afa6593f15e1e79ecb3cf22fc56191cecb452bb0`
through a history-preserving merge.
Its `evalDistEq_simulateQ_run` theorem already lifts equality of joint responses
and retained state to adaptive clients. The bridge supplies its pointwise
premise from the finite-word correspondence; no second probability semantics
or PolyFun-level security layer is needed. Foundation is independently pinned
at `7d0528bd998682788f4e23661f2829298f9e47db`, and Cryptol 3.6.0 at
`61dd17b0c45ddf8c5c1e952afd5e789c4dc4ec4b`. Cryptol's existing `:extract-coq`
typed-AST export can supply the narrow importer, while concrete root type
checks discharge constraints erased by that export. This is a trusted frontend
boundary, followed by kernel-checked finite lowering and specification transfer.
The consumer includes all six SHA-256 word functions, the actual local round,
and full compression. Its preserved source retains the recursive schedule and
fold. Strict-prefix uniqueness, a constructor-producing fixed-point rule, and
fold induction certify the finite implementation; byte-loading and imperative
loop invariants connect it to VCVio's actual `Sha2.compress` at arbitrary valid
offsets. Generic data contracts cover arrays and tupled arguments; adaptive
probabilistic replacement uses the existing VCVio theorem. Padding and full
hashing remain separate obligations.

The native compression test also exercises proved compiler simplifications for
`Fin.cases`, `Fin.cons`, and `Matrix.vecCons`, staged in
`ToCslib/Data/Fin/Cases.lean`. The pinned induction-based implementation computes
discarded recursive results under strict evaluation; nested vector constructors
compound that work. The replacement selects the case directly. Remove the
staging laws when core and Mathlib supply equivalent compiled implementations.

The substitution milestone adds generic `ScopedFamily.Term.map_congr`,
position-based `ScopedDomain.Env.Pointwise`, strict transport of simultaneous
fixed points, and pointed-domain heterogeneous equality lemmas to PolyFun.
Cryptol-specific binder squares, scheme transport, constructor compatibility
and both semantic substitution theorems remain in VCVio Model. The
[scoped roadmap](https://github.com/Verified-zkEVM/PolyFun/blob/main/PolyFunCryptol/docs/model.md#audited-next-milestones) assigns future frontend,
reference-correspondence, compiler and export work without introducing a second
syntax carrier, CPO class or probability interpretation.
