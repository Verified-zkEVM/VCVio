# 7. Quantum time-lock puzzle experiments

Covers: honest generation, quantum preprocessing and retained memory. Includes endpoint security for the idealized masked chain.
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

## The idealized masked-chain puzzle

`MaskedChainPuzzle.scheme q` instantiates this interface with `q + 1` masked links over a
finite abelian group. `MaskedChainPuzzle.gen` samples `q + 2` independent uniform vertices
and queries all chain inputs together. It publishes the first vertex and the masks
`H(xᵢ) + xᵢ₊₁`, retains the full tuple as the auxiliary secret, and uses the final vertex
as the recovery key. The online adversary receives only the public puzzle.

The honest solver follows the links in order: query the current vertex, subtract its
oracle answer from the next public mask, then continue at the recovered successor.
The actual algorithms have the following proved budgets:

| Algorithm | Oracle rounds | Total queried points | Certificate |
|---|---:|---:|---|
| generator | `1` | `q + 1` | `MaskedChainPuzzle.scheme_gen_queryBound` |
| solver | `q + 1` | `q + 1` | `MaskedChainPuzzle.scheme_solve_queryBound` |

Local sampling uses no oracle calls. Each solver round queries one point. The correctness
theorem `MaskedChainPuzzle.evalDist_scheme_solve_publicPuzzle` gives a point-mass law at the
sampled endpoint for every fixed function and hidden tuple, including repeated vertices.

`MaskedChainPuzzle.adversary` embeds an online family without preprocessing, preserving its
initial quantum register and substate. `MaskedChainPuzzle.qromDelayAdvantage_eq_recoveryAdvantage`
identifies the named scheme's two-phase recovery probability with the
[endpoint game](5-qrom.md#endpoint-recovery-for-an-idealized-masked-chain). This equality needs
no adversary query bound and retains one function for honest generation and online queries,
with the full hidden tuple jointly sampled with the masks and endpoint check.

`MaskedChainPuzzle.qromDelayAdvantage_le_root` applies the root-accumulated endpoint bound
to the named scheme: an adversary using at most `q` online rounds of width at most `k` has
recovery probability at most `min 1 (Quantum.MaskedChain.rootRecoveryBound G q k)`.
Generation is outside its online clock, and missing mass counts as failure. The adapter's
preprocessing point budget is zero (`MaskedChainPuzzle.adversary_isQueryBound`).
`MaskedChainPuzzle.qromDelayAdvantage_le` retains the event-error bound.

## Query-bounded preprocessing security

`Quantum.MaskedChain.PreprocessingAdversary` is the full two-phase adversary type for the
idealized puzzle. Its preprocessing output may select both a retained quantum register and
an unrestricted classical state. Its online program can depend on these and on the public
puzzle. The entire adversary and initial state are fixed before the oracle is sampled.

Use `preprocessedRecoveryAdvantage_le_root` to combine preprocessing and online root errors.
With `N = |G|`, write

\[
 A_{\rm on}=N^{-1/2}
 +2\sum_{h=0}^{q-1}\sqrt{k(q-h)/N},\qquad
 \beta=\binom{q+1}{2}/N.
\]

Preprocessing with at most $r_{\mathrm{pre}}$ rounds and $Q_{\mathrm{pre}}$ points, followed by at
most `q` online rounds of width at most `k`, has recovery probability at most

\[
 \min\left\{1,\;\beta+
   \left(A_{\rm on}+2\sqrt{r_{\rm pre}Q_{\rm pre}(q+1)/N}\right)^2\right\}.
\]

The expression inside the minimum is `rootPreprocessedRecoveryBound`. The guessing term
remains explicit, and the collision allowance stays outside the square. The proof compares preprocessing under two
oracles that differ on the freshly sampled chain inputs, keeping the hidden tuple joint
with the endpoint event. The reference preprocessing may depend on the base oracle. The
conditional online bound scales with each retained state's raw mass; summing those masses
charges the online bound once, without conditioning on survival.

`preprocessedRecoveryAdvantage_le_root_min` replaces `rpre` by `min rpre Qpre`.
Width-zero calls can make the original round count exceed the point count.
`dropEmptyPreprocessing` removes them while preserving the complete run, including retained
state, and leaves at most $Q_{\mathrm{pre}}$ nonempty rounds.

`MaskedChainPuzzle.qromDelayAdvantage_eq_preprocessedRecoveryAdvantage` identifies this game
with the actual three-phase scheme experiment, for every two-phase adversary and without
resource assumptions. `MaskedChainPuzzle.qromDelayAdvantage_le_of_preprocessing_root`
transfers the round-aware root bound. `MaskedChainPuzzle.qromDelaySecure_root` establishes
`QROMDelaySecure` for every adversary satisfying a `DelayBudget` whose online round bound is
at most `q`, using `min rpre Qpre`. The online point bound is an additional admissibility
restriction; the online error uses rounds and width.

The event-error APIs remain valid: `preprocessedRecoveryAdvantage_le` adds
`4 * sqrt(rpre * Qpre * (q+1) / N)` to `recoveryBound`; its `_min` version uses
`min rpre Qpre`. `preprocessedRecoveryAdvantage_le_points` needs only a preprocessing point
bound and adds `4 * Qpre * sqrt((q+1) / N)`. Their scheme counterparts include
`MaskedChainPuzzle.qromDelayAdvantage_le_of_preprocessing`,
`MaskedChainPuzzle.qromDelaySecure` and `MaskedChainPuzzle.qromDelaySecure_points`.

Auxiliary-input security remains a separate target. Its advice budget must count all retained
information, including the classical branch state. See the
[model distinction and references](../../design/quantum-layer.md#16-auxiliary-input-security-remains-separate).

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
| the named masked-chain puzzle's two-phase recovery experiment and its endpoint game | `MaskedChainPuzzle.qromDelayAdvantage_eq_recoveryAdvantage` |
| the named puzzle with arbitrary preprocessing and the complete endpoint game | `MaskedChainPuzzle.qromDelayAdvantage_eq_preprocessedRecoveryAdvantage` |
