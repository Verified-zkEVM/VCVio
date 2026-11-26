# Interop/Squirrel

The logic of the Squirrel prover in VCVio: its higher-order CCSA logic, embedded deeply on
PolyFun's scoped syntax, with a semantics over VCVio's machines and the soundness of its rules. It
is a sub-project of [`Interop/`](../README.md), whose index states the rules all sub-projects
share. The design, the rules proved so far and the modelling choices are in the
[design record](../../docs/design/interop-squirrel.md).

## Connects to

- **Squirrel's logic as published** ([`REFERENCES.md`](../../REFERENCES.md)): the base logic of
  [BC14](../../REFERENCES.md#bc14), the higher-order logic of [LICS23](../../REFERENCES.md#lics23)
  (its author report, 30 pp.), the order bounds of [CSF24](../../REFERENCES.md#csf24) (long
  version) and [CCS26](../../REFERENCES.md#ccs26) (ePrint 2026/1912, the authors' PDF of
  2026-09-07). The prover itself is [SP21](../../REFERENCES.md#sp21).
- **The Squirrel tool** ([SQUIRREL-REPO](../../REFERENCES.md#squirrel-repo)) is a secondary
  reference. Where it and a paper differ, the paper is the target, and the difference is a row of
  the design record's obligations table. No code of the tool enters the repository.
- **Lean and Mathlib** v4.36.0 and the root's PolyFun, the root's pins, so the sub-project shares
  the root's dependency cache.

## Trusted base

Nothing beyond Lean. The package requires only VCVio, and no outside code or extraction enters the
repository: the papers' definitions are restated in Lean, and their rules are proved against that
semantics.

## Assumptions

The modelling choices are the rows of the design record's
[obligations table](../../docs/design/interop-squirrel.md#9-obligations): what each Lean definition
takes a paper's definition to mean, where the papers leave it informal or where the formalization
chooses. Among them:
- machines are free programs over a tape interface and an input interface, and the class of
  admitted machines is a parameter: polynomial time is not imposed;
- the attacker tape is a uniform bitstring of a length the model chooses, read bit by bit;
- the honest tape has one uniform bit block per name and index, and a name runs the sampler of its
  type on its block;
- `adv` applies to terms of order at most two and `∼` to vectors of order at most one;
- freshness of names is syntactic: a fresh term does not use the name at all;
- the encryption rule assumes one-time IND-CPA for the reduction of each admitted machine, and
  equal message lengths in every admitted model.

## Implementations covered

None yet: the sub-project states the logic and proves its rules.

## What is proved

| Module | Content |
|---|---|
| `Interop.Squirrel.Syntax` | simple types with the labels `finite`, `fixed` and `large`, declarations, and local terms as one scoped signature |
| `Interop.Squirrel.Model` | models: carriers of bitstrings, the attacker tape, the honest tape of bit blocks, names, labels; the pointwise reading `interp`; β and the semantic core of local rewriting; argument spines of attacker functions of tuples (`Ty.splitArgs`) |
| `Interop.Squirrel.RandomVariable` | local terms as random variables (`rvInterp`), and locality (`eval_denote_rvInterp`) |
| `Interop.Squirrel.Machine` | machines as `OracleComp` programs over the tape and input interfaces, their runs, the denotations `Machine.test` and `AdvMachine.eval`; handlers and the constructions `rename`, `app`, `fn`, `subst`, `branch` and `const` with their runs; the reductions `ite`, `guard` and `adv`; running a machine inside a reduction (`Machine.simulate`); read and query bounds, kept by every construction |
| `Interop.Squirrel.Indist` | advantage, the class of admitted machines `AdvClass` with the closure fields of the rules' reductions, the class `AdvClass.all` of machines with polynomial read and query bounds, `adv` and `∼`; the named reductions as distinguishers, and the laws of `∼` with the advantage kept or bounded at every `η` |
| `Interop.Squirrel.Global` | global formulas as the sum of the local and global signatures, their semantics, validity, and the rules G.Axiom, G.Weak, G.Cut, G.L-∀̃, G.R-∀̃, L.ByGlob and G.ByLoc |
| `Interop.Squirrel.Avoids` | terms that do not use a set of names (`FTerm.AvoidsNames`), stated on PolyFun's `Term.heads` and decidable; such a term ignores the honest-tape coordinates of those names |
| `Interop.Squirrel.Rules.Local` | L.R-∀ |
| `Interop.Squirrel.Rules.Equiv` | Refl, Sym, Trans, G.Equiv:FA-App, FA-Fn, G.Equiv:FA-Adv, BC14's FA, Restr, Perm, Dup, If, G.Case-Study:ITE, BC14's If1, rewriting under an overwhelming equality and Eq1 |
| `Interop.Squirrel.Rules.Rename` | renaming the names of a closed vector along a bijection of names, in every model |
| `Interop.Squirrel.Rules.Enc` | BC14's EncCCA1 without decryption, from one-time IND-CPA through the named reduction `EncSymbols.encReduction`, with the advantages equal at every `η` |
| `Interop.Squirrel.Derivation` | derivations of these rules as data, the encryption rule at the admitted instances, and `Derivation.sound` |

The declarations are in the namespace `Interop.Squirrel`. CI's axiom sweep holds every root of
`InteropSquirrel` at zero `sorry` and nonstandard-axiom debt.

## Stability

Beyond the [stability](../README.md#stability) of `Interop/`, this sub-project follows the papers
it formalizes rather than a tool release: a new version of a paper can change a rule's statement
and the obligations table. A rule whose proof builds a reduction asks the class of machines to
admit that reduction, through a field of `AdvClass`; such a rule changes `AdvClass`, and every
class built in a check meets the new field.

## Build and test

```bash
cd Interop/Squirrel
lake exe cache get
lake build      # VCVio and the library InteropSquirrel
lake test       # the library InteropSquirrelTest
```

The library `InteropSquirrel` lists the roots. The test library `InteropSquirrelTest`, the
package's test driver, holds the checks:
- validity is not trivial (`Interop/Squirrel/Test/Validity.lean`);
- read and query bounds count what they claim, with negative cases
  (`Interop/Squirrel/Test/Bounds.lean`);
- one small derivation per structural rule, with checks that premises are needed
  (`Interop/Squirrel/Test/Structural.lean`);
- each closure field of `AdvClass.all`, at a machine built by its construction
  (`Interop/Squirrel/Test/Constructions.lean`);
- reused encryption randomness breaks indistinguishability, and name renaming
  (`Interop/Squirrel/Test/TwoTimePad.lean`);
- the case split and If1, with countermodels for a missing condition or premise
  (`Interop/Squirrel/Test/CaseStudy.lean`);
- the encryption rule: the one-time pad meets its hypotheses, and countermodels for a leaky scheme,
  a key equal to the coin and reused coins (`Interop/Squirrel/Test/EncExamples.lean`);
- the derivation `pk(k), enc(n; r), n ∼ pk(k), enc(zero; r), n` with its soundness, and a pad that
  leaks lengths (`Interop/Squirrel/Test/WorkedEnc.lean`).

CI's `Interop Squirrel` job builds the package, runs `lake test` and sweeps the roots of
`InteropSquirrel` for axioms.
