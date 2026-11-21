# VCVioFrontier

## Start with the one-time pad

The pad’s polynomial interface `coinSpec` has one request, `()`, with response type `Bool`.
The CSLib free tree `encryptWord msg` asks once for each message bit and returns the
coordinatewise XOR of the answers with the message. Choose how to answer those requests
by installing a PolyFun handler. VCVio spells that fold `simulateQ`.

From a separate checkout for the nested package, run the worked example from the repository root.

```sh
cd VCVioFrontier && lake exe cache get && lake build VCVioFrontierTest.Examples.OneTimePad
```

To print the first result, save the snippet below to a scratch file and run
`lake env lean /path/to/PadReview.lean` from the nested package.
[Open the Lean example](VCVioFrontierTest/Examples/OneTimePad.lean)

```lean
import VCVioFrontier.Examples.OneTimePad.Machine
open VCVioFrontier.OneTimePad

#eval (simulateQ tapeBits (encryptWord [false, true, false])).run [true, false, false, true]
-- some ([true, true, false], [true])
```

The tape supplies the key `[true, false, false]`. The ciphertext is `[true, true, false]` and
the final `true` is still on the tape. Try changing the first key bit to `false` and updating the
expected ciphertext in the example. The general law `encryptWord_tapeBits` states the result
for every equal-width key and message and every unused suffix.
[Word program and tape law](VCVioFrontier/Examples/OneTimePad/Words.lean)

Install `fairBits` to interpret **the same** `encryptWord` probabilistically.
`WordMachine.agrees` identifies the output distribution of `encryptMachine` with the law of `simulateQ fairBits (encryptWord msg)`.
Then `encryptMachine_rows` proves that any two messages of the same width give identical
ciphertext distributions, including at width zero.

1. PolyFun models the local functions as scoped terms. The pair of variables is
   `(msg, key)`. Encryption evaluates `key xor msg` and the full round trip evaluates
   `key xor (key xor msg)`. In PolyFunFrontier, Samuel Schlesinger’s `polytime` tactic from
   cslib-frontier proves the primitive word-operation bound. `wordTerm_polyTime` gives the bound
   for the entire term. [Scoped word terms](https://github.com/dtumad/PolyFun/blob/7c69cdbf24a1865bc7544496ef6d3b9fa746c2a3/PolyFunFrontier/PolyFunFrontier/IPFunctor/Scoped/PolyTime.lean)
2. PolyFunFrontier combines these local steps with the fair-bit handler. It noncomputably
   chooses a finite-control probabilistic multi-tape machine whose output law agrees with the handler on encoded
   inputs. Its polynomial clock bounds every supported run on every input word.
   The explicit key sampler has the required output law at clock `n + 1` on unary input `n`.
   The encryption machine has its own polynomial clock.
   [Pad machines and correctness](VCVioFrontier/Examples/OneTimePad/Machine.lean)
3. `encryptWord_eq` identifies the tree with VCVio’s encryption experiment. The pad’s
   perfect-secrecy theorem, `oneTimePad.denote_coinOneTimePad_cipherGivenMsg_eq_uniform`,
   proves its ciphertext is uniform for every message. `encryptWord_law` transports this
   distribution to words. `WordMachine.output_law` identifies it with the output measure
   of the same machine that has the halting proof.
   [Original uniform-ciphertext proof](../Examples/OneTimePad/ComputationalComplexity.lean) ·
   [Machine and handler measure](VCVioFrontier/OracleComp/Realization.lean)

## Build

The nested package follows PolyFunFrontier's immutable pins. At this revision it uses Lean
4.36.0-rc2 and the root packages use stable 4.36.0. Use a separate worktree for the nested
build, since the path dependency on VCVio writes into the parent directory's `.lake/build`.

```sh
cd VCVioFrontier
lake exe cache get
python3 ./scripts/check-pins.py
lake build VCVioFrontier VCVioFrontierTest
lake exe mk_all --lib VCVioFrontier --module --check
lake exe axiomsweep --root VCVioFrontier --baseline ../scripts/axiom_baseline.json --check
```

The pin check requires Python 3.11 or newer. After publishing a new PolyFun revision, run
`python3 ./scripts/check-pins.py --sync-from /path/to/PolyFun <commit>` here to update the
two PolyFun dependencies, Frontier, CSLib, Mathlib and the toolchain together.
