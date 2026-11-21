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
   for the entire term. [Scoped word terms](https://github.com/dtumad/PolyFun/blob/01547e783a20b7c3acee3137acf96d6c7fabbb7b/PolyFunFrontier/PolyFunFrontier/IPFunctor/Scoped/PolyTime.lean)
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

## Follow the ElGamal reduction

In VCVio’s one-time IND-CPA game, the adversary chooses two messages and saves state, then
guesses which message was encrypted. The reduction runs that adversary on a Diffie–Hellman
challenge. Its result is whether the guess matched the challenge bit.
[Native game](../VCVio/CryptoFoundations/AsymmEncAlg/INDCPA/OneTime.lean) ·
[Original algebraic reduction](../Examples/ElGamal/Basic.lean)

From the nested package, run `lake build VCVioFrontierTest.Examples.ElGamal.Branches VCVioFrontierTest.Examples.ElGamal.State`.
To inspect the result and its security bound, put the following in the same kind of scratch file
as the pad example and run `lake env lean /path/to/ElGamalReview.lean`.

```lean
import VCVioFrontierTest.Examples.ElGamal.Branches
import VCVioFrontier.Examples.ElGamal.Bound

#check VCVioFrontierTest.ElGamal.incorrectGuessLoses
#check VCVioFrontier.ElGamal.AdversaryRealization.implemented_advantage_le
```

1. **Install the adversary and coin handlers.** The typed open reduction and the encoded request
   tree `reductionSource` share the choose, coin and guess steps. `oneTimeChoice` translates
   VCVio’s first message on a true bit to Frontier’s `msg₁`. In `incorrectGuessLoses` the
   handler offers zero and the generator, supplies a false bit, receives the saved state and
   the ciphertext of zero, and guesses true. The reduction therefore returns false.
   [Original open reduction](../Examples/ElGamal/ComputationalComplexity.lean) ·
   [Encoded requests and handlers](VCVioFrontier/Examples/ElGamal/Reduction.lean) ·
   [Losing encoded run](VCVioFrontierTest/Examples/ElGamal/Branches.lean)
2. **Identify the machine.** A realization `R` supplies uniform polynomial-time word procedures
   for the two adversary stages. Its choose law preserves both messages and their saved state
   jointly. Its guess law agrees on encoded states and ciphertexts. `machine_output_openOracle`
   identifies the output of `R.machine` at its certified clock with the encoded result of the
   original handled reduction. The clock bounds supported runs on every input word.
   `eval_ddhReduction_fixedBits` also identifies the reducer’s law with the fair mixture of
   Frontier’s two fixed-bit distinguishers after scoring their guesses.
   [Machine correspondence](VCVioFrontier/Examples/ElGamal/Security.lean) ·
   [Fixed-bit comparison](VCVioFrontier/Examples/ElGamal/Reduction.lean) ·
   [Frontier’s distinguisher](https://github.com/cslib-community/cslib-frontier/blob/87063d8acdd04168e47c55701c7497de584af566/CslibFrontier/Crypto/Computational/ElGamal.lean#L606)
3. **Install the exponent handler in the honest algorithms.** Fixed exponents recover every
   encoded group-element message for every secret and nonce. A stateful tape handler feeds these
   exponents to key generation and encryption. Decryption draws nothing from the remaining tape. Installing Frontier’s bounded fair-coin
   sampler gives the three fields of the implemented word scheme. If selecting the group
   description from the security parameter is polynomial time, `wordScheme_efficient`
   certifies all three fields, including the option-valued plaintext returned by decryption.
   [Honest programs and sampler equations](VCVioFrontier/Examples/ElGamal/HonestPrograms.lean) ·
   [Implemented algorithms](VCVioFrontier/Examples/ElGamal/Honest.lean) ·
   [Tape-handler round trip](VCVioFrontierTest/Examples/ElGamal/State.lean) ·
   [Frontier’s bounded algorithms](https://github.com/cslib-community/cslib-frontier/blob/87063d8acdd04168e47c55701c7497de584af566/CslibFrontier/Crypto/Computational/ElGamal/ProbComp.lean)
4. **Read the bound at a single parameter.** With exact exponents, `R.advantage_eq` gives
   exactly twice the DDH advantage of this adversary’s named distinguisher. Each bounded
   fixed-bit game incurs error at most `2 / 2^n`. Together these give
   `R.implemented_advantage_le`, bounding the original VCVio game by `2 * AdvDDH + 4 / 2^n`.
   Both statements hold before assuming DDH.
   [Original factor-of-two proof](../Examples/ElGamal/Basic.lean) ·
   [Exact-exponent machine games](VCVioFrontier/Examples/ElGamal/Security.lean) ·
   [Implemented advantage](VCVioFrontier/Examples/ElGamal/Bound.lean)

For asymptotic security, assume uniform machine DDH for a prime-order group family with a fixed
public description at each security parameter. For bit messages, `bitAdversary_secure` covers
every uniform strict-PPT two-stage bit-message adversary. For guarded word messages,
`wordGame_measure_negligible` covers every uniform strict-PPT word adversary when the
polynomial-time guard accepts only group-element encodings. For the unguarded group-message
game, `implemented_secureAgainst` covers word adversaries realizing a typed adversary as in
step 2. [Bit and guarded-word theorems](VCVioFrontier/Examples/ElGamal/Honest.lean) ·
[Unguarded security theorem](VCVioFrontier/Examples/ElGamal/Bound.lean) ·
[Uniform DDH assumption](https://github.com/cslib-community/cslib-frontier/blob/87063d8acdd04168e47c55701c7497de584af566/CslibFrontier/Crypto/Computational/DiffieHellman.lean#L338)

## Build

The stable root, its Interop consumer, and this optional package currently use the same PolyFun
commit. The root and Interop resolve core PolyFun on Lean 4.36.0. The nested package selects
PolyFunFrontier and cslib-frontier on their own Lean 4.36.0-rc2, CSLib and Mathlib pins. Use a separate worktree for the nested
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
