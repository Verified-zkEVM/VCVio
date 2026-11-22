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
Proved sound, each as a lemma about validity and as a constructor of derivations (section 8): the
structural rules of [LICS23, Fig. 7]; the rules about `∼` that need no cryptographic assumption,
from [BC14, Fig. 2] and [LICS23], among them the case split; name renaming; and
[BC14]'s encryption axiom EncCCA1 without decryption, from one-time IND-CPA. The rules about `adv`
and deduction, the other cryptographic rules and the secrecy judgments are not formalized here.

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

**Constructions.** Every construction on machines is a handler for the input interface of one
machine into the interface of another (`Handler`), applied by `Machine.handle`: relabelling the
inputs along a renaming (`Machine.rename`), answering an input of type `b` by querying an input of
type `a → b` at the value of a Boolean or base input (`Machine.app`), answering an input by an
honest symbol (`Machine.fn`), and answering the first input by running another machine on the
query's arguments and the remaining inputs (`Machine.subst`). A machine may also branch on a
Boolean input (`Machine.branch`) or return a constant (`Machine.const`). Each construction has a
`run` lemma, proved from what its handler evaluates to (`Handler.EvalsTo`), and keeps read and
query bounds; a handler multiplies a query bound by the number of queries its answers make. The
reductions of the rules (`Machine.ite`, `Machine.guard`, `Machine.adv`) are built from these. A
cryptographic reduction runs a machine as a program inside its own oracle computations
(`Machine.simulate`); answered from values, the run is the machine's run at those values
(`Machine.simulate_ofVals`).

Two bounds describe a machine without a model of time. `Machine.ReadsBelow A b` says that every
tape read of `A`, on every path, is below `b η` (VCVio's `AllQueriesSatisfy`); then `A`'s run
depends on the tape only through those bits (`Machine.ReadsBelow.run_eq`). `Machine.QueryBound A q`
says that `A` makes at most `q η` input queries on every path (VCVio's `IsQueryBoundP`; tape reads
are not counted). A machine running in time `t` meets both with `t`.
`Interop/Squirrel/Test/Bounds.lean` checks that each bound counts what it claims, with a negative
case for each.

## 4. The class of machines

`AdvClass M` is a predicate on the machines of a model, with closure fields, and the semantics of
`adv` and `∼` quantifies over its members: `C.Adv X` says that an admitted machine computes `X`
everywhere, and `C.Indist u v` that every admitted machine has negligible advantage between `u`
and `v`. The class
stands for LICS23's polynomial-time machines, but polynomial time is not imposed: the class is a
parameter of validity (L14). `AdvClass.all` admits every machine with polynomial read and query
bounds; it is the class of the satisfiability checks and countermodels.

**How the class grows.** A rule whose proof turns an attacker against its conclusion into attackers
against its premises needs the class to admit those reductions. Such a rule adds a field to
`AdvClass`, which names the program construction it admits and the property of a class of
polynomial-time machines that gives it, and comes with that construction and its run lemma.
`AdvClass.all` meets every field, so a rule's hypotheses can be shown jointly satisfiable against
it. A bound becomes a field only when a rule uses it on every admitted machine. No field admits an
`η`-indexed constant: the values a field supplies are Booleans, the model's honest symbols and the
arguments of a machine's own queries.

| Field | Construction | Rules | Polynomial-time counterpart |
|---|---|---|---|
| `rename_mem` | `Machine.rename` | Perm, Restr, Dup; with the fields below, FA-Adv, If and the case split | a handler forwarding each query along the renaming, one query per query |
| `subst_mem` | `Machine.subst` | FA-Adv | VCVio's handler closure with a certificate for the handler, sequenced by `IsOraclePPTBy.bind`; answers are Boolean or base values |
| `app_mem` | `Machine.app` | FA-App | a handler making two queries per query |
| `fn_mem` | `Machine.fn` | FA-Fn, and through it [BC14]'s FA | a pure polynomial-time function of the query, since honest symbols are interpreted by polynomial-time functions |
| `branch_mem` | `Machine.branch` | If, the case split, If1 | one query, then either machine |
| `const_mem` | `Machine.const` | the case split, If1 | a constant |

The structural rules, name renaming and the encryption rule need no field: renaming gives every
machine advantage zero, and the encryption rule states its assumption for the reduction of each
admitted machine. Two pieces are present without a field. The input projection `Machine.input` is
a member of `AdvClass.all`, which the checks use; the read and query bounds define `AdvClass.all`
and are checked on their own. `Interop/Squirrel/Test/Constructions.lean` checks each field of
`AdvClass.all` at a machine built by its construction.

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

The rules about `∼` follow the pattern with factor one. FA, If, Restr, Perm and Dup each name one
reduction whose advantage against the premise equals the attacker's against the conclusion at
every `η` (`advantage_app`, `advantage_rename`, …). The case split names two, `Machine.guard true`
and `Machine.guard false`, which return `false` when the condition fails; the attacker's advantage
is at most the sum of theirs at every `η` (`advantage_cons_cond_le`, L7). Name renaming is a
permutation of the honest tape's coordinates, under which the uniform tape is invariant, so every
machine has advantage zero (L16). The encryption rule's reduction `EncSymbols.encReduction` draws
both tapes itself and runs the attacker's machine on the public key, the challenge and the
context; at every `η` its one-time IND-CPA advantage equals the attacker's advantage (L17).

**Freshness.** The honest tape has one coin per name and index, and a name reads only the coins
of its own slots, so freshness of names is syntactic. `FTerm.AvoidsNames N t` says that no head of
`t`, in the sense of PolyFun's `Term.heads`, is the constructor of a name in `N`. It is a fold over
the term, decidable for a decidable `N`, so `decide` checks it on concrete terms; and PolyFun's
`Term.denote_update_eq` gives that such a term ignores every coordinate of the honest tape that
belongs to a name in `N` (`FTerm.denote_update_eq_of_avoidsNames`), with no induction over terms.
The encryption rule's side conditions are of this kind (L22). Not using a name at all is stronger
than not reading the coordinate a given occurrence reads; no rule here needs the weaker, semantic
form.

## 7. Derivations as data

`Derivation D Θ F` is an inductive type with one constructor per rule, indexed by the context, the
hypotheses and the conclusion; local sequents are unfolded to the global sequents they stand for.
`Derivation.sound R C` maps every derivation to `Valid R C Θ F`, one rule lemma per constructor,
for every model restriction and every class of machines. Derivations are data: Lean functions can
build them, for example by recursion on a protocol's trace, and the kernel checks them. A rule with
a semantic side condition takes it as a premise of its constructor.

The encryption rule is a constructor at the instances that a parameter `enc` admits
(`Derivation D enc Θ F`). Its syntactic side conditions (`EncInstance.Syntactic`: distinct key and
coin names, which the messages and the context do not use) are a premise of the constructor, which
`decide` discharges on concrete instances; `Derivation.sound` takes the semantic hypotheses of each
admitted instance (`EncInstance.Holds`: equal message lengths in every admitted model, and one-time
IND-CPA for the reductions of the admitted machines). With `enc` empty, derivations use the other
rules only. [BC14]'s If1 is a constructor although the case split proves it: deriving it would
rewrite `if c' then z else z` to `z`, and the fragment has no rule proving that local equality.

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
| Refl, Sym, Trans | [BC14, Fig. 2] | `Valid.equiv_refl`, `Valid.equiv_symm`, `Valid.equiv_trans` | `Derivation.equivRefl`, `Derivation.equivSymm`, `Derivation.equivTrans` |
| G.Equiv:FA-App | [LICS23] | `Valid.equiv_app` | `Derivation.equivApp` |
| FA-Fn | [LICS23] | `Valid.equiv_fn` | `Derivation.equivFn` |
| G.Equiv:FA-Adv | [LICS23] | `Valid.equiv_adv` | `Derivation.equivAdv` |
| FA, for an honest symbol | [BC14, Fig. 2] | `Valid.equiv_fa` | `Derivation.equivFn`, then `Derivation.equivApp` |
| Restr | [BC14, Fig. 2] | `Valid.equiv_tail` | `Derivation.equivTail` |
| Perm | [BC14, Fig. 2] | `Valid.equiv_rename` | `Derivation.equivRename` |
| Dup | [BC14, Fig. 2] | `Valid.equiv_dup` | `Derivation.equivDup` |
| If (FA for the conditional) | [BC14, Fig. 2] | `Valid.equiv_ite` | `Derivation.equivIte` |
| G.Case-Study:ITE | [LICS23, Fig. 8] | `Valid.equiv_caseStudy` | `Derivation.equivCaseStudy` |
| If1 | [BC14, Fig. 2, Proposition 2] | `Valid.equiv_if1` | `Derivation.equivIf1` |
| Rewriting under `[t = t']` | [LICS23] (G.Rewrite) | `Valid.equiv_rewrite` | `Derivation.equivRewrite` |
| Eq1 | [BC14, Fig. 2] | `Valid.equiv_eq_self` | `Derivation.equivEqSelf` |
| Name renaming | [BC14] | `Valid.equiv_renameNames_of_equiv` | `Derivation.equivRenameNames` |
| EncCCA1 without decryption | [BC14, §7, Proposition 3]; [LICS23, Proposition 19] | `Valid.equiv_enc` | `Derivation.equivEnc` |

`Interop/Squirrel/Test/Structural.lean` builds a small derivation for each structural rule, and
checks that a premise is needed: `[false]` follows from the hypothesis `[false]` but not from none,
and `[∀ (x : bool). x = true]` is not valid. The checks of the other rules are countermodels and
satisfiability models:
- `Test/TwoTimePad.lean`: the one-bit pad with a fresh pad gives indistinguishable encryptions,
  with a reused pad it does not, and renaming exchanges the two pads;
- `Test/CaseStudy.lean`: If1 at a random condition that both branches read, as a derivation; the
  case split without the condition beside each branch is unsound; neither premise of If1 may be
  dropped; and the case split's reduction changes the output;
- `Test/EncExamples.lean`: the one-time pad meets every hypothesis of the encryption rule, and the
  conclusion fails for a scheme that leaks the message, for a key name equal to the coin name and
  for coins in the context, the last two rejected by `decide`;
- `Test/WorkedEnc.lean`: the derivation `pk(k), enc(n; r), n ∼ pk(k), enc(zero; r), n` with its
  soundness, and a pad that leaks lengths, which meets the rule's hypotheses although it fails the
  unrestricted IND-CPA game.

## 9. Obligations

Each row is a point where the papers leave something informal or where the formalization makes a
modelling choice. A row is closed only by a Lean theorem, or a countermodel, named in its last
column. The ids are stable: a row keeps its id when rows are added, so the ids here are not
contiguous. Every name in the last column is in the namespace `Interop.Squirrel`.

| Id | Kind | Source anchor | Obligation | Status | Lean anchor |
|---|---|---|---|---|---|
| L7 | gap | [LICS23] Fig. 8; [BC14] Prop. 2 | LICS23 gives no proof of G.Case-Study:ITE and refers to BC14, whose Prop. 2 proves only If1, with one condition and one context on both sides. Its machines flip a coin when the condition fails, and their success probability, written `1/4 + p`, holds only when the condition is true with probability one half; the error cancels because the condition is shared, and would not with two conditions. The case split is proved here with two conditions, by two named reductions that return `false` when the condition fails, with the advantage at most the sum of the premises' advantages at every `η` (factor one; BC14's factor two comes from naming one of the two machines). If1 is its instance with both right-hand branches equal. A countermodel shows that each premise must keep the condition beside its branch. | closed (case split) | `advantage_cons_cond_le`, `Valid.equiv_caseStudy`, `Valid.equiv_if1`, `CaseStudy.caseStudy_needs_condition` |
| L10 | choice | [LICS23] p. 5, Fig. 2 (p. 7) | Adversaries read the shared attacker tape `ρa` in the papers, while VCVio adversaries draw fresh coins. Here `ρa` is a uniform bitstring of a length the model chooses (`Model.TapeA`), and machines read it bit by bit through the tape interface (`tapeSpec`), as LICS23's machines read their randomness tape; attacker symbols read the same tape. Relating these machines to VCVio adversaries with fresh coins is open. | open | `Model.TapeA`, `tapeSpec`, `Machine.run` |
| L11 | choice | [LICS23] p. 7; [CSF24] App. A; [CCS26] §3.1 (p. 6) | `∼` at arbitrary order (LICS23) versus order at most 1 for `∼` and at most 2 for `adv` (CSF24, CCS26). The fragment of CSF24 and CCS26 is adopted and made syntactic: the global constructors `adv τs β` and `equiv τs` carry proofs of `Ty.AdvOrder τs β` (the term `τ₁ → … → τₙ → β` has order at most 2) and `Ty.IndistOrder τs` (entries of order at most 1), so an atom outside the fragment cannot be written. The semantics is defined at every type. | closed (adopted fragment) | `GlobalOp`, `Ty.AdvOrder`, `Ty.IndistOrder` |
| L12 | choice | [LICS23] §II-B (pp. 5–6) | Names read the honest tape, a product with one uniform bit block per name and index (`Model.Coin`, `coinLen η τ` bits); a name reads its own block and runs the sampler of its type on it, and names of one type share a sampler, so independence and identical distribution are structural. LICS23 (p. 6) notes that a name needs finitely many bits of the honest tape and requires names to be samplings computable in polynomial time. Neither polynomial bit blocks nor polynomial-time samplers are imposed on models here. | open | `Model.TapeH`, `Model.Coin`, `Model.name` |
| L13 | choice | [LICS23] Fig. 2 | `const t` at arrow types is read as a logical relation (`Ty.Same`). LICS23 asks for a value in `⋂_η ⟦τ⟧_η`; the two agree at base types and at arrows from fixed types, and differ when the domain varies with `η`. | open | `Ty.Same`, `RV.IsConst` |
| L14 | choice | [LICS23] §II-C.1, §II-C.2, Fig. 2 (p. 7) | The machines of `adv` and `∼` are free programs (`OracleComp`) over the sum of a tape interface and an input interface, run by fixed answers. LICS23's machines receive base values as bitstring encodings on input tapes and functions through handles on a query tape; here every input is an oracle that receives and returns typed values, a base input is queried with no arguments, and a query supplies all of a function's arguments (no handles for partial applications, which inputs of order at most 1 do not need). The class `AdvClass` is a predicate on machines, closed under the constructions that the rules' reductions use (section 4), and a parameter of validity: polynomial time is not imposed. `AdvClass.all`, the machines with polynomial read and query bounds, is the class of the satisfiability checks. | open | `Machine`, `Machine.ReadsBelow`, `Machine.QueryBound`, `AdvClass`, `AdvClass.all` |
| L15 | choice | [LICS23] §II-A, §II-B | LICS23's declared variables are split into constructors (names, honest symbols with tape-independent values, attacker symbols reading `ρa`, `=_τ`, `∀_τ`, `∃_τ`) and free variables, which range over all random variables. | open | `Decl`, `localSig` |
| L16 | choice | [BC14] (α-renaming of names); [LICS23] §II-B.2 | Renaming names in a closed vector is sound along any type-preserving bijection of names, in every model: the renaming is the permutation `Model.tapePerm` of the honest tape's coordinates. The residue is the restriction to closed vectors, which LICS23's rule shares (free variables range over all random variables, which may read the tape). | closed | `Model.renamesNames`, `Valid.equiv_renameNames_of_equiv`, `Derivation.equivRenameNames`, `TwoTimePad.valid_swap` |
| L17 | gap | [BC14] §7 (Fig. 2, EncCCA1; Prop. 3); [LICS23] Prop. 19 (G.CCA1) | Soundness of the encryption rule when the secret key is never used to decrypt: `pk(nk), enc(m₀; r, pk(nk)), u⃗ ∼ pk(nk), enc(m₁; r, pk(nk)), u⃗`, in left-or-right form. The key and coin names are distinct; the messages and the context have the public key free and are closed by substituting `pk(nk)`, and they use neither the key name nor the coin name (syntactic side conditions, L22); in every admitted model the two messages have equal length at every tape (a restriction on models). The length condition is BC14's guard `EQL(u, u′)` holding surely, as in LICS23's G.CCA1, where `zero (len m)` has the length of `m` in every model. The assumption is one-time IND-CPA (`IND_CPA_OneTime_Advantage` at `ProbCompRuntime.probComp`) for the image of the class under the named reduction `EncSymbols.encReduction`, which submits only pairs of equal length (it is admissible for the leakage `lenOf`); at every `η` the two advantages are equal. A scheme that leaks lengths meets every hypothesis, though it fails VCVio's unrestricted game. Countermodels show that the IND-CPA hypothesis, the distinct names and the freshness of the coins in the context are each needed. Still open: decryption (IND-CCA1), BC14's guard as a conditional in the conclusion for messages whose lengths differ on some tapes, and the real-or-zero form. | closed (this fragment) | `Valid.equiv_enc`, `EncSymbols.advantage_challenge`, `EncSymbols.encReduction_isAdmissible`, `WorkedEnc.workedDerivation_sound`, `WorkedEnc.valid_worked_lpad`, `WorkedEnc.lpad_advantage_unequalAdv`, `EncExamples.not_valid_enc_leaky`, `WorkedEnc.not_valid_leak`, `EncExamples.not_valid_enc_keyIsCoin`, `EncExamples.not_valid_enc_coinReused` |
| L19 | choice | [LICS23] App. A (label `large`), §II-B.1 | `large` is LICS23's bound `Pr_ρh[⟦n⟧(η, a)(ρh) = b] ≤ 2^{-c·η}` for some real `c > 0`, read on the sampler that names of the type share. LICS23 lifts labels to compound types "in the natural way" without saying how `large` lifts; here Booleans and arrow types are not `large`. A base type labelled `finite`, `fixed` and `large` has no model, so the checks that use the trivial model assume no `large` base type. | open | `Model.IsLarge`, `Ty.HasLabel`, `Model.isLarge_of_hasLabel`, `Model.trivial_respectsLabels` |
| L22 | choice | [BC14] §7 (freshness in EncCCA1) | Freshness side conditions are syntactic: a term avoids a set of names when none of its heads (PolyFun's `Term.heads`) is one of them (`FTerm.AvoidsNames`, `Vec.AvoidsNames`). The condition is a fold over the term and decidable for names with decidable equality, so `decide` checks it on concrete instances (`EncInstance.Syntactic`). It implies the semantic condition that the term's value ignores the honest-tape coordinates of those names (`FTerm.denote_update_eq_of_avoidsNames`, from `Term.denote_update_eq`). Not using a name is stronger than not reading the coordinate of one occurrence: a term that uses the key name at another index fails the check. Countermodels show that the encryption rule's syntactic conditions are needed, and `decide` rejects the instances that break them. | closed (this fragment) | `FTerm.AvoidsNames`, `FTerm.denote_update_eq_of_avoidsNames`, `EncInstance.Syntactic`, `WorkedEnc.workedInstance_syntactic`, `EncExamples.not_keyIsCoin_syntactic`, `EncExamples.not_coinReused_syntactic` |
