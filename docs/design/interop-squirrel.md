# Squirrel's logic in VCVio

Design record of [`Interop/Squirrel`](../../Interop/Squirrel/README.md). Paper keys are those of
[`REFERENCES.md`](../../REFERENCES.md).

## 1. Scope and status

Squirrel is an interactive prover for security protocols in the computational model [SP21]. Its
logic is a CCSA logic. In the base logic of Bana and Comon-Lundh [BC14], terms stand for
probabilistic polynomial-time computations, and `u⃗ ∼ v⃗` says that no polynomial-time attacker
tells two vectors of terms apart. [LICS23] makes the logic higher-order: local terms are simply
typed λ-terms read as families of random variables, and global formulas are first-order formulas
about them, with `∼`, `adv`, `const` and the overwhelming truth `[φ]` of a local formula as atoms.
[CSF24] and [CCS26] restrict `adv` and `∼` to low orders, and [CCS26] adds secrecy judgments.

`Interop/Squirrel` embeds this logic deeply. The syntax is PolyFun's scoped syntax, the semantics
is defined in Lean over models of random tapes and machines that are VCVio programs, and each rule
of the logic is a Lean theorem about that semantics. The target is the rules as the papers state
them, not the tool's implementation of them.

Status. The sub-project holds the syntax, the models, local terms as random variables, machines
with read and query bounds, the class of admitted machines, global formulas and their validity.
The structural rules of [LICS23, Fig. 7] are proved sound, each as a lemma about validity and as a
constructor of derivations (section 8). The rules about `∼` and `adv`, the cryptographic rules and
the secrecy judgments are not formalized here.

## 2. Syntax and models

**Types and declarations.** `Ty B` holds the simple types over base types `B`, with `bool` built
in. A declaration `Decl B` gives each base type its labels (`finite`, `fixed`, `large`), the names
`n : a → b` with finite index types, the honest function symbols of each type and the attacker
function symbols. `Ty.HasLabel` lifts `finite` and `fixed` along arrows; `large` holds only of
base types declared `large` (L19).

**Local terms.** The local terms are the terms of one monomorphic `ScopedSignature`, `localSig D`,
over the sorts `Kind B`: a local type, or `glob`, the sort of global formulas. Its constructors are
application, abstraction (the only binder), the conditional, `true`, `false`, `=_τ`, `∀_τ`, `∃_τ`,
the names and the declared symbols. Variables, renaming, capture-avoiding substitution and folds
are PolyFun's. LICS23 treats `=_τ`, the quantifiers, names and symbols as declared variables with
restricted models; here they are constructors, and the other declared variables are free variables
(L15).

**Models.** A model gives, at each security parameter `η`:
- each base type a nonempty set of bitstrings;
- the attacker tape `Model.TapeA M η`, a bitstring of a length `lenA η` that the model chooses
  (L10);
- the honest tape `Model.TapeH M η`, a product with one bit block per name and index
  (`Model.Slot`), of `coinLen η τ` bits for a name of type `τ`; a name reads its own block and runs
  the sampler of its type on it, so samplings of distinct name-index pairs are independent and
  those of one type identically distributed (L12);
- each honest symbol a value, and each attacker symbol a function of the attacker tape.

Both tapes are drawn uniformly, with VCVio's `$ᵗ`.

**Readings.** `interp M η ρ` reads local syntax at one parameter and pair of tapes: `bool` is
`Bool`, arrows are full function spaces, and `=_τ` and the quantifiers decide their propositions
classically. `rvInterp M` reads it as random variables, one family per type; an abstraction binds
`RV.constAt η a`, LICS23's `1^η_a`. Locality (`eval_denote_rvInterp`) says that a random
variable at `(η, ρ)` is the pointwise reading of the environment's values there; its proof is
PolyFun's relational fold `IFreeM.fold_rel`, with no induction on terms. β
(`LTerm.denote_app_lam`, `LTerm.denote_rvInterp_app_lam`) and the semantic core of local
rewriting (`LTerm.denote_substOne_congr`) follow from PolyFun's substitution lemma.

## 3. Machines

LICS23's machines for `adv` and `∼` read the attacker tape from a randomness tape and query their
inputs through a query tape. Here a machine `Machine M τs β` is, at each `η`, a VCVio program
`OracleComp (M.Iface η τs) _` over the sum of two interfaces:
- the tape interface `tapeSpec`, whose query `i` reads bit `i` of the attacker tape (`false` past
  its end);
- the input interface `Model.inSpec M η τs`, whose query to an input of type `τ` carries values for
  all of `τ`'s arguments and is answered by a value of its result type. A Boolean or base input is
  queried with no arguments (L14).

`Machine.run` answers the tape from a tape and the inputs from values (VCVio's
`evalWithAnswerFn`). The semantics uses two denotations: `Machine.test`, a distinguisher, and
`AdvMachine.eval`, the curried attacker function that a machine for `adv` computes. A machine is a
program rather than a function of its inputs so that a construction on machines is a program
transformation, a handler applied by `simulateQ`, which a class of polynomial-time machines can
certify from the machine's program.

Two bounds describe a machine without a model of time. `Machine.ReadsBelow A b` says that every
tape read of `A`, on every path, is below `b η` (VCVio's `AllQueriesSatisfy`); then `A`'s run
depends on the tape only through those bits (`Machine.ReadsBelow.run_eq`). `Machine.QueryBound A q`
says that `A` makes at most `q η` input queries on every path (VCVio's `IsQueryBoundP`; tape reads
are not counted). A machine running in time `t` meets both with `t`.
`Interop/Squirrel/Test/Bounds.lean` checks that each bound counts what it claims, with a negative
case for each.

## 4. The class of machines

`AdvClass M` is a predicate on the machines of a model, and the semantics of `adv` and `∼`
quantifies over its members: `C.Adv X` says that an admitted machine computes `X` everywhere, and
`C.Indist u v` that every admitted machine has negligible advantage between `u` and `v`. The class
stands for LICS23's polynomial-time machines, but polynomial time is not imposed: the class is a
parameter of validity (L14). `AdvClass.all` admits every machine with polynomial read and query
bounds; it is the class of the satisfiability checks and countermodels.

**How the class grows.** A rule whose proof turns an attacker against its conclusion into attackers
against its premises needs the class to admit those reductions. Such a rule adds a field to
`AdvClass`, which names the program construction it admits and the property of a class of
polynomial-time machines that gives it, and comes with that construction and its run lemma.
`AdvClass.all` meets every field, so a rule's hypotheses can be shown jointly satisfiable against
it. A bound becomes a field only when a rule uses it on every admitted machine.

The structural rules need no field, so `AdvClass` has only membership. Two pieces are present
without a field. The input projection `Machine.input` is a member of `AdvClass.all`, which the
check `Valid.not_equiv_tt_ff` uses; the read and query bounds define `AdvClass.all` and are checked
on their own.

## 5. Validity

**Global formulas.** The global constructors (`globalSig B`) are truth, falsity, the connectives,
the global quantifiers `∀̃`, `∃̃` over random variables of a local type, `[φ]`, `const`, `adv` and
`∼`. The full signature `fullSig D` is the sum of the local and global signatures over the same
sorts (PolyFun's `ScopedSignature.sum`), so global quantifiers bind variables that local terms
use, as in LICS23's environments, and substitution of local terms into global formulas is
PolyFun's. `adv` and `∼` carry the order bounds of CSF24 and CCS26 (`Ty.AdvOrder`,
`Ty.IndistOrder`), so an atom outside that fragment cannot be written (L11).

**Semantics.** `fullInterp M C` reads local constructors as random variables and global ones as
propositions. `[φ]` is `Overwhelming`: over uniform tapes, the probability that `φ` is false is
negligible. `const t` is `RV.IsConst` (L13), `adv` is `C.Adv` and `∼` is `C.Indist`. Substitution
does not keep local terms inside global formulas in the image of `Term.inl`, so locality is proved
again for the full signature (`eval_denote_fullInterp`).

**Validity.** `Valid R C Θ F` says that in every model respecting the labels and the restriction
`R`, against the class `C M`, at every value of the variables, `F` holds wherever every formula
of `Θ` holds. A local sequent `Θ; Γl ⊢ φ` is `Θ ⊢ [∧Γl ⇒ φ]` (`LValid`).

**Satisfiability.** The trivial model (`Model.trivial`, in the tests) has one empty bitstring per
carrier and empty tapes. It respects every label but `large`, so for a declaration with no `large`
base type validity does not quantify over an empty class of models (L19). In it `[false]` is not
valid (`Valid.not_box_ff`), and `true ∼ false` is not valid against `AdvClass.all`
(`Valid.not_equiv_tt_ff`): the input projection has advantage one.

## 6. The proof pattern

Each rule is a theorem about `Valid`, proved against the semantics. A rule about `∼` or `adv` is
proved through named reductions: machines built from an attacker against the conclusion and
admitted by fields of the class. The proof first bounds the attacker's advantage against the
conclusion at every `η` by the advantages of the named reductions against the premises, plus any
explicit error terms. The asymptotic rule then follows from the closure of negligible functions
under sums. A cryptographic rule states its assumption for the named reduction, never for every
adversary of a type.

The structural rules need no reduction. Their proofs are about hypotheses and substitution
(`Term.denote_substOne`, `Term.denote_rename`). L.R-∀ uses the choice construction of [LICS23,
Proposition 2]: the variable of the premise is instantiated by a random variable that picks, at
each parameter and tape, a counterexample when one exists.

## 7. Derivations as data

`Derivation D Θ F` is an inductive type with one constructor per rule, indexed by the context, the
hypotheses and the conclusion; local sequents are unfolded to the global sequents they stand for.
`Derivation.sound R C` maps every derivation to `Valid R C Θ F`, one rule lemma per constructor,
for every model restriction and every class of machines. Derivations are data: Lean functions can
build them, for example by recursion on a protocol's trace, and the kernel checks them. A rule with
a semantic side condition takes it as a premise of its constructor.

## 8. Rules

| Rule | Source | Validity | Constructor |
|---|---|---|---|
| G.Axiom | [LICS23, Fig. 7] | `Valid.ax` | `Derivation.ax` |
| G.Weak | [LICS23, Fig. 7] | `Valid.weaken` | `Derivation.weaken` |
| G.Cut | [LICS23, Fig. 7] | `Valid.cut` | `Derivation.cut` |
| G.L-∀̃ | [LICS23, Fig. 7] | `Valid.all_left` | `Derivation.allLeft` |
| G.R-∀̃ | [LICS23, Fig. 7] | `Valid.all_right` | `Derivation.allRight` |
| L.ByGlob | [LICS23, Fig. 7] | `Valid.byGlob` | `Derivation.byGlob` |
| G.ByLoc | [LICS23, Fig. 7] | `Valid.byLoc` | `Derivation.byLoc` |
| L.R-∀ | [LICS23, Fig. 7, Proposition 2] | `Valid.local_all` | `Derivation.localAll` |

`Interop/Squirrel/Test/Structural.lean` builds a small derivation for each, and checks that a
premise is needed: `[false]` follows from the hypothesis `[false]` but not from none, and
`[∀ (x : bool). x = true]` is not valid.

## 9. Obligations

Each row is a point where the papers leave something informal or where the formalization makes a
modelling choice. A row is closed only by a Lean theorem, or a countermodel, named in its last
column. The ids are stable: a row keeps its id when rows are added, so the ids here are not
contiguous. Every name in the last column is in the namespace `SquirrelLogic`.

| Id | Kind | Source anchor | Obligation | Status | Lean anchor |
|---|---|---|---|---|---|
| L10 | choice | [LICS23] p. 5, Fig. 2 (p. 7) | Adversaries read the shared attacker tape `ρa` in the papers, while VCVio adversaries draw fresh coins. Here `ρa` is a uniform bitstring of a length the model chooses (`Model.TapeA`), and machines read it bit by bit through the tape interface (`tapeSpec`), as LICS23's machines read their randomness tape; attacker symbols read the same tape. Relating these machines to VCVio adversaries with fresh coins is open. | open | `Model.TapeA`, `tapeSpec`, `Machine.run` |
| L11 | choice | [LICS23] p. 7; [CSF24] App. A; [CCS26] §3.1 (p. 6) | `∼` at arbitrary order (LICS23) versus order at most 1 for `∼` and at most 2 for `adv` (CSF24, CCS26). The fragment of CSF24 and CCS26 is adopted and made syntactic: the global constructors `adv τs β` and `equiv τs` carry proofs of `Ty.AdvOrder τs β` (the term `τ₁ → … → τₙ → β` has order at most 2) and `Ty.IndistOrder τs` (entries of order at most 1), so an atom outside the fragment cannot be written. The semantics is defined at every type. | closed (adopted fragment) | `GlobalOp`, `Ty.AdvOrder`, `Ty.IndistOrder` |
| L12 | choice | [LICS23] §II-B (pp. 5–6) | Names read the honest tape, a product with one uniform bit block per name and index (`Model.Coin`, `coinLen η τ` bits); a name reads its own block and runs the sampler of its type on it, and names of one type share a sampler, so independence and identical distribution are structural. LICS23 (p. 6) notes that a name needs finitely many bits of the honest tape and requires names to be samplings computable in polynomial time. Neither polynomial bit blocks nor polynomial-time samplers are imposed on models here. | open | `Model.TapeH`, `Model.Coin`, `Model.name` |
| L13 | choice | [LICS23] Fig. 2 | `const t` at arrow types is read as a logical relation (`Ty.Same`). LICS23 asks for a value in `⋂_η ⟦τ⟧_η`; the two agree at base types and at arrows from fixed types, and differ when the domain varies with `η`. | open | `Ty.Same`, `RV.IsConst` |
| L14 | choice | [LICS23] §II-C.1, §II-C.2, Fig. 2 (p. 7) | The machines of `adv` and `∼` are free programs (`OracleComp`) over the sum of a tape interface and an input interface, run by fixed answers. LICS23's machines receive base values as bitstring encodings on input tapes and functions through handles on a query tape; here every input is an oracle that receives and returns typed values, a base input is queried with no arguments, and a query supplies all of a function's arguments (no handles for partial applications, which inputs of order at most 1 do not need). The class `AdvClass` is a predicate on machines and a parameter of validity: polynomial time is not imposed. `AdvClass.all`, the machines with polynomial read and query bounds, is the class of the satisfiability checks. | open | `Machine`, `Machine.ReadsBelow`, `Machine.QueryBound`, `AdvClass`, `AdvClass.all` |
| L15 | choice | [LICS23] §II-A, §II-B | LICS23's declared variables are split into constructors (names, honest symbols with tape-independent values, attacker symbols reading `ρa`, `=_τ`, `∀_τ`, `∃_τ`) and free variables, which range over all random variables. | open | `Decl`, `localSig` |
| L19 | choice | [LICS23] App. A (label `large`), §II-B.1 | `large` is LICS23's bound `Pr_ρh[⟦n⟧(η, a)(ρh) = b] ≤ 2^{-c·η}` for some real `c > 0`, read on the sampler that names of the type share. LICS23 lifts labels to compound types "in the natural way" without saying how `large` lifts; here Booleans and arrow types are not `large`. A base type labelled `finite`, `fixed` and `large` has no model, so the checks that use the trivial model assume no `large` base type. | open | `Model.IsLarge`, `Ty.HasLabel`, `Model.isLarge_of_hasLabel`, `Model.trivial_respectsLabels` |
