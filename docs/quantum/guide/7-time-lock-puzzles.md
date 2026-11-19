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
preprocessing budgets.

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
 \beta=\binom{q+2}{2}/N.
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
The exact `PointerChainPuzzle` construction has a separate finite-window theorem below.

## Finite windows for the exact pointer-chain encoding

The exact pointer-chain construction has ordinary hash chains, an accumulator and a public
commitment, in addition to masked links. `PointerChainPuzzle.LeanSeal.quantumWindowScheme`
gives its honest algorithms a concrete quantum-oracle interface. Its recovery bound uses
rank-cutoff hybrids over the complete raw oracle, rather than the idealized chain theorem.

The raw input register is `ByteArray.Bounded`: every byte string up to the stated maximum
length. It includes malformed encodings and inputs outside the six typed hash domains.
The response register contains all 32 bytes, including the bytes discarded by honest mask
truncation. `hashInputBound` is `max (54+b) 83`; every honest input fits, and 86 bytes suffices
when the link width is at most 32. An adversary may query any superposition within the window.
The interface does not model unrestricted-length byte queries.

`windowTableEquiv` splits the complete raw table into typed answers, fixed mask tails and
all outside-image answers. `sampledDelayLawWith_quantumWindowScheme` transports the entire
preprocessing/generation/online experiment through that bijection. Its observer retains the
answering table jointly with the transcript. `qromDelayAdvantage_quantumWindowScheme` is the
key-recovery specialization. Neither equality assumes query budgets or bounds the success
probability.

The honest generator and checked solver agree with the source leanSeal algorithms for
every fixed byte-answer function, restricted to the window. The public puzzle is the
existing structured `PointerChainPuzzle.LeanSeal.Puzzle` type. Transport to serialized public
puzzles and a statement for arbitrary serialized solver inputs remain separate; the honest oracle-input
encoding alone does not establish that wire interface.

The rank-frontier lemmas provide another prerequisite. A path input for the next honest
query round depends only on labels received in preceding honest rounds; inputs further
ahead have an unreached predecessor and a bounded per-point incidence. The commitment's
output is already public, while its input contains the secret key. The reference prefix oracle
leaves its prescribed response unprogrammed until its honest receipt rank; queries to that cell
receive the base-table response. Resampling future words preserves the reached full responses,
their raw tails and the public commitment value.

The rank-ordered programming coupling is proved separately.
`PointerChainPuzzle.LeanSeal.qromDelayAdvantage_quantumWindowScheme_le_programmed` bounds
actual recovery by `programmedWindowRecoveryAdvantage + solvePoints(n,m)^2 / |Bytes 32|`.
The programmed game samples full raw path responses independently and uses the resulting
completed oracle for both adversary phases. Its preprocessing memory is retained, and the
hidden key remains joint with the endpoint event. The path-input collision allowance is
charged once; the path responses are not conditioned on collision-freedom.

This comparison needs no adversary query budget. The resource-bounded rank analysis below
controls the programmed game. See the
[coupling specification](../../design/quantum-layer.md#18-rank-ordered-programming-coupling)
for the causal order, collision event and preprocessing conventions.

## Finite-window quantum recovery bound

Write `S = |Bytes 32|`, `L = |Bytes b|`, `A = |Bytes 16|` and `P = solvePoints(n,m)`. The
online and preprocessing incidence coefficients are

```
δ_on  = [n ≥ 2] / L + P / S
δ_pre = A⁻¹ * (L⁻¹ + P / S).
```

`rankRecoveryBound b n m r k` is the online bound
`B_on = (S^(-1/2) + r * sqrt(4*k*δ_on))²`. It holds before the honest key round, for input
states independent of the fresh challenge words conditional on the base oracle. The proof
averages square-root probabilities through the rounds and squares only at the end.

`qromDelayAdvantage_quantumWindowScheme_le_of_preprocessing` bounds the actual experiment by

```
min 1 (P²/S + (sqrt(B_on) + 2*sqrt(rpre*Qpre*δ_pre))²).
```

Preprocessing has at most $r_{\mathrm{pre}}$ rounds and $Q_{\mathrm{pre}}$ points; every online
continuation has at most `r` rounds and width at most `k`, with `r < keyRound n m`.
The parameter assumptions are
`n ≠ 0`, `n < 2^32`, `b ≤ 32` and a window containing all honest inputs. One function answers
all three phases. Classical and quantum preprocessing memory are unrestricted, and failed
branches count as failure. `qromDelaySecure_quantumWindowScheme` establishes `QROMDelaySecure`
for every admissible `DelayBudget`. The online point budget is an additional restriction;
the bound uses online rounds and width.

The preprocessing hybrid compares the completed programmed oracle with the base oracle
while retaining the complete online continuation as the common finishing operation. A
reference preprocessing state can depend on that base oracle, but not on the fresh challenge
coins. The online bound scales with each branch's successful mass, so summing retained
branches charges it once. The path-input collision allowance `P²/S` stays outside the square;
no hidden word is conditioned on collision-freedom.

Salt-free later accumulator inputs constrain two independent fresh 32-byte state labels,
which suffice for their incidence bound. See the [rank-security specification](../../design/quantum-layer.md#19-finite-window-rank-security-with-preprocessing)
for the separate oracle-family cases.

The honest solver derives the key after `keyRound n m = n*(m+2)+1` rounds. Its checked version
makes one extra commitment-validation call. The security threshold uses the key's own round.
The following examples use $r_{\mathrm{pre}}Q_{\mathrm{pre}}\le 2^{100}$ and
`r = keyRound n m - 1`. Maximum work means `n = 2^20`, `m = 2^40`; moderate depth means
`n = 2`, `m = 2^29 - 2`.

| Chain work | Link bytes | Online rounds | Width | Full capped bound |
|---|---:|---|---|---|
| maximum | `32` | `2^60 + 2^21` | `2^40` | about `2^-34` |
| moderate | `16` | `2^30` | `2^20` | about `2^-46` |
| maximum | `16` | `2^60 + 2^21` | `2^40` | `1` (vacuous) |

The [detailed parameter table](../../design/quantum-layer.md#20-concrete-finite-window-query-estimates)
also gives the honest path-point counts and separates collision and preprocessing cross terms.
The bound is independent of the chosen finite window length. It concerns structured public
puzzles and programs bounded on every online branch; arbitrary serialized puzzle parsing,
quantum truncation for early success, and unrestricted-length oracle queries need separate
transport or execution results. Unbounded preprocessing with bounded advice remains separate.

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
| the finite-window pointer puzzle experiment and full raw-table completion | `PointerChainPuzzle.LeanSeal.sampledDelayLawWith_quantumWindowScheme` |
