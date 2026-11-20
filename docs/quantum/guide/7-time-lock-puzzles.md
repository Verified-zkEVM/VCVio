# 7. Quantum time-lock puzzle experiments

Covers: honest generation, quantum preprocessing, retained memory, exact finite-window encoding
and its programmed-oracle coupling.
Read first: [programs and runtimes](4-programs-and-runtimes.md) and [the QROM](5-qrom.md).

## A challenge generated between two adversary phases

A delay experiment first lets the adversary preprocess its oracle. The challenger then
generates a public puzzle and a hidden key. The adversary resumes with its retained quantum
memory, classical preprocessing state and public puzzle, and tries to output the key.
The online clock starts when the puzzle is published.

`Quantum.TimeLockPuzzle` describes the honest generator and solver. The generator returns
the public puzzle, recovery key and an auxiliary classical `Secret`. This secret can retain
a whole sampled chain for analysis even when the adversary outputs only its endpoint.
The generator starts and ends on the trivial register, discarding its internal workspace.
The solver returns `Option Key` so that malformed puzzles can have no solution.

`TwoPhaseAdversary` gives each preprocessing branch its own retained quantum register and
classical state. Its online algorithm receives that state and the public puzzle. The key
and auxiliary secret are accessible to the analysis observer, but are not inputs to the
online algorithm. `TwoPhaseAdversary.withoutPreprocessing` runs an online algorithm
immediately from its fixed initial register and substate.

## One oracle state throughout

`generationInstrument` runs honest generation on the runtime's private register with the
adversary's memory as a spectator. `delayInstrument` composes preprocessing, generation and
online execution on that same private register. This matters for a compressed or purified
oracle: preprocessing can correlate the adversary's retained memory with the database, and
generation must act on that correlated joint state.

`delayLawWith` supplies the initial product state once and observes a `DelayTranscript`.
The transcript retains the preprocessing branch, puzzle, key, auxiliary secret and final
output. The law is a subprobability measure. Missing mass counts as failure, without
renormalization. For lossless phase instruments, its total mass is exactly the product of
the initial adversary and oracle masses (`delayLawWith_apply_univ_of_lossless`).

`sampledDelayLawWith` averages complete experiments over a single runtime parameter.
`qromDelayAdvantage` uses one uniformly sampled function for preprocessing, generation and
online execution. The puzzle, adversary and initial state are fixed before that sampling.
Recovery compares only the output with the actual key.

## Resources and classical generators

`DelayBudget` separates preprocessing rounds and points from online rounds, points and maximum width.
`TwoPhaseAdversary.IsQueryBound` imposes these bounds on every possible continuation,
including branches of weight zero. Honest generation consumes none of the online budget.
This is query-bounded preprocessing with unrestricted retained classical and quantum memory.
It differs from auxiliary-input security, which permits unbounded preprocessing and limits
the advice retained for the online attack.
`QROMDelaySecure` quantifies over adversaries satisfying such a budget; it is a security
target to establish from an oracle argument. Assuming it for the puzzle under analysis
would assume the required delay bound. A theorem about a named adversary adapter establishes
the predicate only after proving that the adapter covers all admissible two-phase adversaries.

Classical honest puzzles embed through `TimeLockPuzzle.toQuantum`, preserving generation
round and point bounds. `Quantum.TimeLockPuzzle.ofClassicalGenerator` also allows arbitrary
hidden classical generator data. `delayLawWith_ofClassicalGenerator` expresses the complete
observed law as a classical generator average of online laws starting from the actual
preprocessing post-states under the same fixed function. The observer may jointly inspect
the preprocessing branch, key, secret and final leaf. `delayLawWith_ofClassicalGenerator_eq_sum`
fuses preprocessing and online execution when the observer uses only generator data and the
final leaf. Its key-recovery corollary is `delayAdvantage_ofClassicalGenerator`.

That averaging result uses the trivial private register of a fixed-function runtime.
The underlying instrument factorization, `delayInstrument_withoutPreprocessing`, applies to
stateful runtimes too and keeps their private state throughout.

The corresponding laws without preprocessing remain available. A theorem proved only for
that restricted adversary class does not establish `QROMDelaySecure` for arbitrary
preprocessing budgets. The interface embeds classical honest generators; an adapter from
arbitrary classical two-phase adversaries, preserving both advantages and resource budgets,
is a separate bridge. Generic correctness and solver-budget predicates for quantum puzzles
are also separate interface work. The application below proves its honest execution
laws and budgets directly.

## Finite windows for the exact pointer-chain encoding

The exact pointer-chain construction has ordinary hash chains, an accumulator and a public
commitment, in addition to masked links. `PointerChainPuzzle.LeanSeal.quantumWindowScheme`
gives its honest algorithms a concrete quantum-oracle interface. A resource-bounded quantum recovery theorem requires additional rank-cutoff analysis.

The raw input register is `ByteArray.Bounded`: every byte string up to the stated maximum
length. It includes malformed encodings and inputs outside the six typed hash domains.
The response register contains all 32 bytes, including the bytes discarded by honest mask
truncation. `hashInputBound` is `max (54+b) 83`; every honest input fits, and 86 bytes suffices
when the link width is at most 32. An adversary may query any superposition within the window.
The interface does not model unrestricted-length byte queries.

The raw interface supplies `quantumWindowScheme`, the injective honest-input encoding
`hashInputWindow_injective`, and the fixed-oracle honest execution equalities
`simulateQ_windowScheme_gen` and `simulateQ_windowScheme_solve`. The coupling
programs the raw table directly, so the adversary retains all raw query registers throughout.

Separately, `windowTableEquiv` splits that table into typed answers, fixed mask tails and
all outside-image answers. `sampledDelayLawWith_quantumWindowScheme` transports the complete
experiment through this bijection, and `qromDelayAdvantage_quantumWindowScheme` specializes
it to key recovery. These standalone encoding laws retain the answering table jointly with
the transcript and require no query budget. These table-splitting laws are separate from the raw
encoding and programming interfaces.

The honest generator and checked solver agree with the source leanSeal algorithms for
every fixed byte-answer function, restricted to the window. The public puzzle is the
existing structured `PointerChainPuzzle.LeanSeal.Puzzle` type. Transport to serialized public
puzzles and a statement for arbitrary serialized solver inputs remain separate; the honest oracle-input
encoding alone does not establish that wire interface.

`quantumWindowDerive` exposes honest key derivation without the commitment check.
`isTotalQueryBound_quantumWindowDerive` gives its `keyRound n m = n*(m+2)+1` round bound,
and `evalDist_quantumWindowDerive_genWith` gives the point-mass law at the actual generated
key for every fixed raw oracle and honest generation coins. The checked solver makes one
extra commitment-validation call.

The rank-frontier lemmas provide another prerequisite. A path input for the next honest
query round depends only on labels received in preceding honest rounds; inputs further
ahead have an unreached predecessor and a bounded per-point incidence. The commitment's
output is already public, while its input contains the secret key.

The rank-ordered programming coupling is proved separately.
`PointerChainPuzzle.LeanSeal.qromDelayAdvantage_quantumWindowScheme_le_programmed` bounds
actual recovery by `programmedWindowRecoveryAdvantage + solvePoints(n,m)^2 / |Bytes 32|`.
The programmed game samples full raw path responses independently and uses the resulting
completed oracle for both adversary phases. Its preprocessing memory is retained, and the
hidden key remains joint with the endpoint event. The path-input collision allowance is
charged once; the path responses are not conditioned on collision-freedom.

This comparison needs no adversary query budget. A resource-bounded quantum analysis of the programmed game remains separate. See the
[coupling specification](../../design/quantum-layer.md#18-rank-ordered-programming-coupling)
for the causal order, collision event and preprocessing conventions.

## Checks

The library relates the phase composition to its observed laws without introducing separate
oracle initializations:

| Two descriptions | Agreement |
|---|---|
| three-phase execution without preprocessing and generation followed by online execution | `delayInstrument_withoutPreprocessing` |
| a classical honest generator and its quantum execution under a fixed function | `generationInstrument_ofClassicalGenerator_branch` |
| a classical generator after arbitrary quantum preprocessing and the joint phase average | `delayLawWith_ofClassicalGenerator` |
| key recovery with arbitrary preprocessing and the classical generator average | `delayAdvantage_ofClassicalGenerator` |
| the joint delay observation and the classical average of online observations | `delayLawWith_withoutPreprocessing_ofClassicalGenerator` |
| key recovery and the classical average of online key guesses | `delayAdvantage_withoutPreprocessing_ofClassicalGenerator` |
| the finite-window pointer puzzle experiment and full raw-table completion | `PointerChainPuzzle.LeanSeal.sampledDelayLawWith_quantumWindowScheme` |
