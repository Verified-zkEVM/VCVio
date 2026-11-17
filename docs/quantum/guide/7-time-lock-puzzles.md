# 7. Quantum time-lock puzzle experiments

Covers: honest generation, quantum preprocessing, retained memory, and endpoint recovery.
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

`DelayBudget` separates preprocessing points from online rounds, points and maximum width.
`TwoPhaseAdversary.IsQueryBound` imposes these bounds on every possible continuation,
including branches of weight zero. Honest generation consumes none of the online budget.
`QROMDelaySecure` quantifies over adversaries satisfying such a budget; it is a security
definition, not a theorem that every puzzle satisfies it.

Classical honest puzzles embed through `TimeLockPuzzle.toQuantum`, preserving generation
round and point bounds. `Quantum.TimeLockPuzzle.ofClassicalGenerator` also allows arbitrary
hidden classical generator data. For adversaries without preprocessing,
`delayLawWith_withoutPreprocessing_ofClassicalGenerator` expresses the complete observed law
as a classical generator average of online laws under the same fixed function. The observer
may jointly inspect the key, secret and final leaf. The key-only corollary is
`delayAdvantage_withoutPreprocessing_ofClassicalGenerator`.

That averaging result uses the trivial private register of a fixed-function runtime.
The underlying instrument factorization, `delayInstrument_withoutPreprocessing`, applies to
stateful runtimes too and keeps their private state throughout.

The experiment interface permits preprocessing. A security theorem proved only for an
online adversary without preprocessing does not establish `QROMDelaySecure` for arbitrary
preprocessing budgets.

## Checks

The library relates the phase composition to its observed laws without introducing separate
oracle initializations:

| Two descriptions | Agreement |
|---|---|
| three-phase execution without preprocessing and generation followed by online execution | `delayInstrument_withoutPreprocessing` |
| a classical honest generator and its quantum execution under a fixed function | `generationInstrument_ofClassicalGenerator_branch` |
| the joint delay observation and the classical average of online observations | `delayLawWith_withoutPreprocessing_ofClassicalGenerator` |
| key recovery and the classical average of online key guesses | `delayAdvantage_withoutPreprocessing_ofClassicalGenerator` |
