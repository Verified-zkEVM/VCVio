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
  equal message lengths in every admitted model;
- `⊬` and `▷` are derived formulas, with a curried attacker function of the tuple on the left;
  Rw-Equiv is proved for a right side of Boolean or base type;
- FreshL assumes models whose attacker tape is eventually longer than every polynomial and whose
  names of the fresh type read polynomially many bits, and terms that read the attacker tape below
  a polynomial; it draws the fresh name from the attacker tape of the same model;
- Rw-Oracle is proved as CCS26's double rule and Pc-Oracle from it, for oracles with a Boolean or
  base argument and a right side of Boolean or base type, under FreshL's conditions on models and
  terms for the oracles' argument type; the guessed query position is uniform below the power of
  two above the query bound, and the guess draws its default with the sampler of the argument
  type;
- G.PRF is proved without the hash oracle on the left, for a vector and a message given as
  first-order terms with explicit hash calls in the `⊢pptm` fragment, of Boolean or base types,
  with `ψ_msg` generated over the call arguments and the conditions of conditionals dropped; the
  key name occurs nowhere but as the key of the hash (`ψ_key`), names of the hash type are uniform,
  and the PRF assumption is a hypothesis on the two named reductions of each admitted machine;
- PRF.R and PRF.L-sec are proved with the hash oracle on the left as the term `λx. h(x, k)`,
  answered in the reductions by the compiled `λx. call x`, under G.PRF's conditions on terms,
  FreshL's conditions on models and terms for messages (and hashes, PRF.L-sec), and a `large` hash
  type (PRF.R); PRF.R's `ψ_msg` ranges over the calls of the vector only, PRF.L-sec is the form of
  CCS26 §2.3, with `ψ_msg` over the calls of the vector, the secret and the message, and the PRF
  assumption is a hypothesis on the named reductions of each admitted machine.

## Implementations covered

None yet: the sub-project states the logic and proves its rules.

## What is proved

| Module | Content |
|---|---|
| `Interop.Squirrel.Syntax` | simple types with the labels `finite`, `fixed` and `large`, declarations, and local terms as one scoped signature |
| `Interop.Squirrel.Model` | models: carriers of bitstrings, the attacker tape, the honest tape of bit blocks, names, labels; the pointwise reading `interp`; β and the semantic core of local rewriting; argument spines and post-composition of attacker functions of tuples (`Ty.splitArgs`, `Ty.postcomp`); the order bounds of `adv`, `∼`, `⊬` and `▷` |
| `Interop.Squirrel.RandomVariable` | local terms as random variables (`rvInterp`), and locality (`eval_denote_rvInterp`) |
| `Interop.Squirrel.Machine` | machines as `OracleComp` programs over the tape and input interfaces, their runs, the denotations `Machine.test` and `AdvMachine.eval`; handlers and the constructions `rename`, `app`, `fn`, `subst`, `branch`, `const`, `eqTest`, `shift` and `sampler` with their runs; the reductions `ite`, `guard`, `adv`, `deduce`, `AdvMachine.comp` and `AdvMachine.freshL`; running a machine inside a reduction (`Machine.simulate`); reading and overwriting a block of the attacker tape (`Model.bitsAt`, `Model.setBlock`); a machine run inside a reduction whose input answers evaluate to values returns its run (`Machine.evalWithAnswerFn_simulate`); read and query bounds, kept by every construction |
| `Interop.Squirrel.Guess` | the guessing machine `Machine.guess`, which returns the argument of the query to its oracle input at a position read from the tape, with its run through VCVio's `runLog` and its read and query bounds; a run that queries an oracle only where it agrees with another is unchanged by swapping them, and so is its log; the averaging over drawn bits (`sum_prEvent_eq_two_pow_mul`) |
| `Interop.Squirrel.Indist` | advantage, the class of admitted machines `AdvClass` with the closure fields of the rules' reductions and polynomial read and query bounds, the class `AdvClass.all` of machines with polynomial read and query bounds, `adv` and `∼`; the named reductions as distinguishers, and the laws of `∼` with the advantage kept or bounded at every `η` |
| `Interop.Squirrel.Global` | global formulas as the sum of the local and global signatures, their semantics, validity, and the rules G.Axiom, G.Weak, G.Cut, G.L-∀̃, G.R-∀̃, L.ByGlob and G.ByLoc |
| `Interop.Squirrel.Avoids` | terms that do not use a set of names (`FTerm.AvoidsNames`), stated on PolyFun's `Term.heads` and decidable; such a term ignores the honest-tape coordinates of those names |
| `Interop.Squirrel.Rules.Local` | L.R-∀ |
| `Interop.Squirrel.Rules.Equiv` | Refl, Sym, Trans, G.Equiv:FA-App, FA-Fn, G.Equiv:FA-Adv, BC14's FA, Restr, Perm, Dup, If, G.Case-Study:ITE, BC14's If1, rewriting under an overwhelming equality and Eq1 |
| `Interop.Squirrel.Rules.Rename` | renaming the names of a closed vector along a bijection of names, in every model |
| `Interop.Squirrel.Rules.Enc` | BC14's EncCCA1 without decryption, from one-time IND-CPA through the named reduction `EncSymbols.encReduction`, with the advantages equal at every `η` |
| `Interop.Squirrel.Secrecy` | CCS26's `⊬` and `▷` as global formulas derived from `∀̃`/`∃̃`, `adv`, `⇒̃`/`∧̃` and `[·]`, read as `AdvClass.NonDed` and `AdvClass.Ded`; the laws of Neg1, Neg2, Ineq, Trans, WeakL, WeakR and Rw-Equiv as inequalities at every `η` with their reductions named |
| `Interop.Squirrel.Rules.Secrecy` | Neg1, Neg2, Ineq, Trans, WeakL, WeakR, Rw-Equiv at Boolean or base types, and `u⃗ ▷ f(u⃗)` from `adv(f)` (CCS26 Fig. 3) |
| `Interop.Squirrel.Rules.Deduce` | deductions of an entry, an honest symbol, an application and a rewritten term; local validity and modus ponens under `[·]` |
| `Interop.Squirrel.Rules.Fresh` | FreshR for a closed vector that does not use a name of a `large` type, and with a semantic freshness premise; a closed term that does not use a name ignores its coordinate (`FTerm.AvoidsNames.freshAt`) |
| `Interop.Squirrel.TapeBounds` | read bounds of random variables and of terms (`FTerm.ReadsPoly`, discharged constructor by constructor and from `adv`), and long attacker tapes (`Model.LongTapes`) |
| `Interop.Squirrel.Rules.FreshL` | FreshL by CCS26's argument, with the fresh name drawn from the attacker tape of the same model: the success probabilities are equal at every large `η` |
| `Interop.Squirrel.Rules.Oracle` | Rw-Oracle as CCS26's double rule and in the form of Fig. 3, and Pc-Oracle, by identical until bad and the guessing reduction `AdvMachine.rwGuess`: at every large `η` the success against `u⃗, o₁ ⊢ v` is at most that against `u⃗, o₂ ⊢ v` plus `2^⌈log₂ q(η)⌉` times the probability that the oracles differ at the guess |
| `Interop.Squirrel.OracleTerm` | terms with explicit calls to a keyed hash (`OTerm`), closed up into the logic's terms (`PRFSymbols.close`); `ψ_key`, `⊢pptm` and being first order as conditions on PolyFun's `Term.heads`, decidable; `ψ_msg` over the arguments of the calls of a vector and a message, or of a vector only (`PRFSymbols.psiMsgVec`); the calls of a call argument |
| `Interop.Squirrel.Compile` | the call-by-value reading of terms with calls as free programs over the honest coins, the attacker tape and a hash oracle: PolyFun's `Term.denoteCBV` at one `CBVInterpretation`; its adequacy, and that a run hashes only arguments of calls, from PolyFun's fundamental lemma `Term.denoteCBV_related`; a candidate among a message and its call arguments that its own run does not hash (`PRFSymbols.exists_unhashed`) |
| `Interop.Squirrel.Rules.PRF` | G.PRF without an oracle on the left, from VCVio's PRF game through the named reductions `PRFSymbols.hashReduction` and `PRFSymbols.freshReduction`: at every `η` the advantage is at most their two PRF advantages plus `Pr[ψ_msg = false]`; PRF-Simple, derived from G.PRF, Perm, FreshL and Rw-Equiv |
| `Interop.Squirrel.Rules.PRFOracle` | PRF.R with the hash oracle `o_h^k = λx. h(x, k)` on the left, answered as an input by the compiled `λx. call x`, through the named reductions `PRFSymbols.rightReduction`, one per candidate: at every large `η` the success is at most `Pr[ψ_msg(u⃗) = false]`, plus `2^⌈log₂ q(η)⌉` times the success of Rw-Oracle's guess against `u⃗, o_h^k ⊢ m`, plus a PRF advantage and `2^{-cη}` per candidate |
| `Interop.Squirrel.Rules.PRFLeft` | PRF.L-sec in the form of CCS26 §2.3, through the named reductions `PRFSymbols.leftReduction` and `PRFSymbols.leftFreshReduction`, which intercept the attacker's oracle at the message: at every large `η` the success is at most `Pr[ψ_msg = false]`, plus their two PRF advantages, plus the success of FreshL's reduction against the premise, plus `2^⌈log₂ q(η)⌉` times the success of the guess against `C_sec` |
| `Interop.Squirrel.Derivation` | derivations of these rules as data, the encryption rule, G.PRF, PRF.R and PRF.L-sec at the admitted instances, PRF-Simple derived, the model restriction `R₀` that FreshL, Rw-Oracle, Pc-Oracle, PRF.R and PRF.L-sec assume, and `Derivation.sound` |

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
  leaks lengths (`Interop/Squirrel/Test/WorkedEnc.lean`);
- the derivation `h(h(k)) ⊬ n` with its soundness, `⊬` not transitive, each secrecy rule and
  deduction used with checks that premises are needed, and FreshR without `large` and FreshL
  without freshness unsound (`Interop/Squirrel/Test/SecrecyExamples.lean`);
- a model with long tapes where every hypothesis of FreshL holds, with a worked derivation
  (`Interop/Squirrel/Test/FreshLExamples.lean`);
- FreshL unsound without long tapes, against the class generated by the closure fields
  (`Interop/Squirrel/Test/FreshLCountermodel.lean`);
- Rw-Oracle's hypotheses holding jointly with a conclusion FreshR does not give, its form in
  Fig. 3, its agreement premise needed, and a worked Pc-Oracle
  (`Interop/Squirrel/Test/OracleExamples.lean`);
- the compiled reading on small terms, with adequacy failing outside `⊢pptm`; G.PRF and a worked
  PRF-Simple with every hypothesis holding jointly in a model whose hash is a perfect PRF; and
  G.PRF failing without `ψ_msg` and without `ψ_key` (`Interop/Squirrel/Test/PRFExamples.lean`);
- two PRF.R steps, and a PRF.R step followed by PRF.L-sec, with every hypothesis holding jointly in
  the same model; PRF.L-sec failing without `ψ_msg`, and PRF.R and PRF.L-sec without their premise
  (`Interop/Squirrel/Test/PRFOracleExamples.lean`).

CI's `Interop Squirrel` job builds the package, runs `lake test` and sweeps the roots of
`InteropSquirrel` for axioms.
