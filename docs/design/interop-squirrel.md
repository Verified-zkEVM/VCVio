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
from [BC14, Fig. 2] and [LICS23], among them the case split; name renaming;
[BC14]'s encryption axiom EncCCA1 without decryption, from one-time IND-CPA; and [CCS26]'s
secrecy judgments `⊬` and `▷` with the rules of its Fig. 3, among them Rw-Oracle and Pc-Oracle,
deductions of terms, and FreshR and FreshL (Fig. 11); and, from VCVio's PRF game, G.PRF without
an oracle on the left, with PRF-Simple derived from it ([LICS23]; [CCS26, Fig. 11]), and PRF.R and
PRF.L-sec, with the hash oracle on the left ([CCS26, Fig. 4, §2.3]).

With these rules the sub-project covers [CCS26]'s secrecy fragment through its motivating example:
the forward secrecy of the toy ratchet of [CCS26, §2] is derived in the logic for every trace given
as a Lean value, the derivation is sound by `Derivation.sound` (`Chain.chainPFS_sound`), and every
hypothesis holds jointly in a model whose hash is a perfect PRF (`ChainModel.valid_chainPFS`).

Open:
- the rest of [LICS23]'s core, among it a syntactic local calculus (local reasoning is read
  semantically here) and the cryptographic rules other than G.PRF and the encryption rule: CCA1
  with decryption, ENC-KP, DDH and INT-CTXT (L6);
- recursion and induction: recursive definitions over timestamps and induction in the logic. The
  ratchet's derivation is built by Lean recursion on a fixed trace (L35);
- the rest of [CCS26]: PRF.L-eq and PRF.L-⊤ (L32), the NoCollision lemmas from collision and
  pre-image resistance (L33), and the post-compromise security case study;
- concrete security: each rule has a bound at every `η`, but `Derivation.sound` concludes
  negligibility only, and no bound is composed along a derivation;
- state: Squirrel's mutable cells. The ratchet's key is a term defined by recursion on the history;
- processes: protocols as processes and their translation into the terms of a trace. The ratchet's
  terms are written from [CCS26, Fig. 2] by hand;
- import of developments written for the Squirrel tool.

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
Boolean input (`Machine.branch`), return a constant (`Machine.const`) or test two Boolean or base
inputs for equality (`Machine.eqTest`, by the decidable equality of Booleans and bitstrings). Two
constructions act on the tape: `Machine.shift off A` moves every tape read of `A` by `off η`, a
handler of the tape interface, and `Machine.sampler b` reads the first `coinLen η b` bits and runs
the model's sampler for names of type `b` on them, as a name does on its block of the honest tape.
The guessing machine `Machine.guess off k ha A d` reads a number `j` from the `k η` bits of the
tape at `off η` (`bitsEquiv`), runs `A` logging its queries (VCVio's `withQueryLog`), and returns
the argument of the `j`-th query to its first input, an oracle with a Boolean or base argument, or
the value of the default `d`; its `run` lemma reads the log of the run (VCVio's `runLog`).
Each construction has a `run` lemma, proved from what its handler evaluates to
(`Handler.EvalsTo`), and keeps read and query bounds; a handler multiplies a query bound by the
number of queries its answers make, and a shift adds its offset to a read bound. The reductions of
the rules (`Machine.ite`, `Machine.guard`, `Machine.adv`, `Machine.deduce`, `AdvMachine.comp`,
`AdvMachine.freshL`, `AdvMachine.rwGuess`) are built from these. A cryptographic reduction runs a
machine as a program inside its own oracle computations (`Machine.simulate`); answered from
values, the run is the machine's run at those values (`Machine.simulate_ofVals`).

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
`η`-indexed constant: offsets are computed from polynomials, and the values a field supplies are
Booleans, the model's honest symbols and samplers, and the arguments of a machine's own queries.

| Field | Construction | Rules | Polynomial-time counterpart |
|---|---|---|---|
| `rename_mem` | `Machine.rename` | Perm, Restr, Dup; with the fields below, FA-Adv, If, the case split, Trans, WeakL, WeakR, Rw-Equiv, FreshL, Rw-Oracle, Pc-Oracle, PRF-Simple, PRF.R, PRF.L-sec and the deductions | a handler forwarding each query along the renaming, one query per query |
| `subst_mem` | `Machine.subst` | FA-Adv, Trans, WeakL, WeakR, Rw-Equiv, FreshL, PRF-Simple, PRF.L-sec, the deduction of an application | VCVio's handler closure with a certificate for the handler, sequenced by `IsOraclePPTBy.bind`; answers are Boolean or base values |
| `app_mem` | `Machine.app` | FA-App, the deduction of an entry or honest symbol of arrow type | a handler making two queries per query |
| `fn_mem` | `Machine.fn` | FA-Fn, and through it [BC14]'s FA; the deduction of an honest symbol | a pure polynomial-time function of the query, since honest symbols are interpreted by polynomial-time functions |
| `input_mem` | `Machine.input` | the deductions of an entry, an honest symbol and an application ([LICS23]'s PT.Input) | one query, whose answer is returned |
| `branch_mem` | `Machine.branch` | If, the case split, If1 | one query, then either machine |
| `const_mem` | `Machine.const` | the case split, If1 | a constant |
| `eqTest_mem` | `Machine.eqTest`, at Boolean or base types | Rw-Equiv, PRF-Simple | equality of Booleans or bitstrings |
| `shift_mem` | `Machine.shift`, by a polynomial offset | FreshL, PRF-Simple, PRF.L-sec | a handler of the tape interface adding the offset, computed from `1^η`, to each read |
| `sampler_mem` | `Machine.sampler`, for a type of order at most one with polynomial bit blocks (`Model.PolyCoins`) | FreshL, PRF-Simple, PRF.L-sec; the default of the guess in Rw-Oracle, Pc-Oracle, PRF.R and PRF.L-sec | the name's polynomial-time sampler after reading its bits: a compatibility condition between model and class, like `fn_mem` for honest symbols |
| `readBound_mem` | (a bound) `Machine.ReadsBelow` at a polynomial | FreshL, PRF-Simple, Rw-Oracle, Pc-Oracle, PRF.R, PRF.L-sec; the read bound of an `adv` term | a machine running in time `t` reads its tape below `t` |
| `queryBound_mem` | (a bound) `Machine.QueryBound` at a polynomial | Rw-Oracle, Pc-Oracle, PRF.R, PRF.L-sec | a machine running in time `t` makes at most `t` queries |
| `guess_mem` | `Machine.guess`, reading `⌈log₂ q(η)⌉` bits at `p(η)` for polynomials `p` and `q`, with an admitted default | Rw-Oracle, Pc-Oracle, PRF.R, PRF.L-sec | the bits read after computing `p(η)` and `⌈log₂ q(η)⌉` from `1^η`, then a handler forwarding each query unchanged and keeping its argument (VCVio's handler closure with a logging handler of constant cost per query; answers are passed on, not copied), and one entry of a list of polynomial length |

The structural rules, name renaming, the encryption rule, G.PRF, Neg1, Neg2, Ineq and FreshR need
no field: renaming gives every machine advantage zero, the encryption rule and G.PRF state their
assumptions for the reductions of each admitted machine, which run the machine inside a VCVio
adversary (`Machine.simulate`) rather than as a machine of the class, Neg1, Neg2 and Ineq use the
witness of a `▷` as it is, and FreshR's bound holds against every function of the attacker tape.
PRF-Simple uses the fields of FreshL and Rw-Equiv. PRF.R and PRF.L-sec need no field of their own:
their PRF assumption is stated for their named reductions, which run the attacker's machine inside
a VCVio adversary, and their bounds on the attacker's queries at the message use Rw-Oracle's guess;
PRF.L-sec also uses FreshL's reduction. Four conditions on models enter with these rules, as
hypotheses on the model restriction rather than on every model: the label `large` (FreshR, PRF.R,
L19), long attacker tapes `Model.LongTapes` and polynomial bit blocks `Model.PolyCoins` (FreshL,
PRF-Simple, Rw-Oracle, Pc-Oracle, PRF.R and PRF.L-sec, L12, L23, L28), and uniform names of the
hash type `Model.UniformSampler` (G.PRF, PRF-Simple, PRF.R and PRF.L-sec, L6).
`Interop/Squirrel/Test/Constructions.lean` checks each field of `AdvClass.all` at a machine built
by its construction.

## 5. Validity

**Global formulas.** The global constructors (`globalSig B`) are truth, falsity, the connectives,
the global quantifiers `∀̃`, `∃̃` over random variables of a local type, `[φ]`, `const`, `adv` and
`∼`. The full signature `fullSig D` is the sum of the local and global signatures over the same
sorts (PolyFun's `ScopedSignature.sum`), so global quantifiers bind variables that local terms
use, as in LICS23's environments, and substitution of local terms into global formulas is
PolyFun's. `adv` and `∼` carry the order bounds of CSF24 and CCS26 (`Ty.AdvOrder`,
`Ty.IndistOrder`), so an atom outside that fragment cannot be written (L11).

**Secrecy judgments.** [CCS26, §3.1] defines `u⃗ ⊬ v` and `u⃗ ▷ v` from the global connectives,
and here they are derived formulas, not constructors: `Form.nonDed u v` is
`∀̃ f. adv(f) ⇒̃ [¬ (f(u⃗) = v)]` and `Form.ded u v` is `∃̃ f. adv(f) ∧̃ [f(u⃗) = v]`. The logic has
no product types, so the tuple on the left is a vector of the types `τs` and `f` has the curried
type `τ₁ → … → τₙ → β`, applied to the vector by `FTerm.apps`. Both carry the order bound
`Ty.SecrecyOrder τs β`: the entries and the right side have order at most one, so that `f` has
order at most two, the bound of `adv` (`Ty.SecrecyOrder.advOrder`). A formula outside that
fragment cannot be written (L18).

**Semantics.** `fullInterp M C` reads local constructors as random variables and global ones as
propositions. `[φ]` is `Overwhelming`: over uniform tapes, the probability that `φ` is false is
negligible. `const t` is `RV.IsConst` (L13), `adv` is `C.Adv` and `∼` is `C.Indist`. The
secrecy judgments mean `C.NonDed` (every admitted attacker machine computes the right side with
negligible probability) and `C.Ded` (some admitted attacker machine computes it with overwhelming
probability), by `Form.holds_nonDed` and `Form.holds_ded`. Substitution does not keep local terms
inside global formulas in the image of `Term.inl`, so locality is proved again for the full
signature (`eval_denote_fullInterp`).

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

**Secrecy.** The rules about `⊬` and `▷` follow the pattern with the success and failure of an
attacker function (`deduceAdv`, `deduceErr`) in place of an advantage. Neg1, Neg2 and Ineq use the
witness of `▷` as it is: success and failure sum to one, and `v` and `w` agree only where the
witness of `u⃗ ▷ w` fails or an attacker computes `v`. Trans, WeakL and WeakR compose two attacker
machines on the same tape (`AdvMachine.comp`), and the failure probabilities add. Rw-Equiv runs the
attacker machine on the left part of the vector and tests its result against the last entry
(`Machine.deduce`), so its success changes by at most that distinguisher's advantage (L21). The
deductions build attacker machines from the input projection, honest symbols and substitution;
local reasoning is read semantically, as a local formula true at every tape of every admitted
model (`Valid.box_valid`), with modus ponens under `[·]`.

**FreshR and FreshL.** FreshR overwrites the name's coordinate of the honest tape with a fresh
coin, which leaves the tape uniform; for each tape, every attacker function hits the coin with at
most the sampler's largest point probability, at most `2^{-cη}` for a `large` type (L19).
FreshL's reduction `AdvMachine.freshL` runs the attacker machine with the fresh name drawn by the
sampler from bits of the attacker tape above a polynomial that bounds what the machine
(`AdvClass.readBound_mem`) and the terms read (`FTerm.ReadsPoly`, L24). Wherever those bits fit on
the tape, swapping them with the name's coordinate is a bijection of the tapes that the machine
and the terms do not see, so the two success probabilities are equal; long tapes make that hold at
every large `η` (L20, L23). No model is extended, unlike [CCS26]'s proof.

**Rw-Oracle and Pc-Oracle: identical until bad, and a guess.** [CCS26, App. C.1] proves Rw-Oracle
as a double rule, whose agreement premise deduces `m` from `u⃗, o_β` for `o_β` either oracle. The
attacker machine `g` is first read as a machine whose first input is the oracle
(`AdvMachine.withOracleFirst`). On one tape, if the run with `o_β` queries the oracle only where
`o₁` and `o₂` agree, the run with the other oracle is the same (`Machine.run_cons_eq_of_firstArgs`,
from VCVio's `evalWithAnswerFn_eq_of_forall_mem_runLog`), so the two successes differ by at most the
probability of a faulty query (`deduceAdv_le_add_faulty`). The faulty query is then guessed: the
reduction `AdvMachine.rwGuess` reads `j` from `⌈log₂ q(η)⌉` bits of the attacker tape above the
read bounds of `g` and of the terms, runs `g` with `o_β`, and returns the argument of its `j`-th
oracle query, or a value drawn by the sampler of the argument type if there is none (L28); `q` is
`g`'s query bound (`AdvClass.queryBound_mem`). `k` bits spell a number uniform below `2^k`
(`bitsEquiv`), and the sum over `j < 2^k` of the probabilities of events that read the tape below
the bits is `2^k` times the probability at the drawn `j`, by one involution that swaps the drawn
bits with that block (`sum_prEvent_eq_two_pow_mul`, `Model.setBlock`). With `j` ranging over
`2^⌈log₂ q⌉ ≤ 2q + 1` positions (`Nat.pow_clog_le_mul_add_one`), the probability of a faulty query
is at most `2^⌈log₂ q(η)⌉` times the probability that the guess is a point where the oracles differ
(`prEvent_faultyAt_le`, L27). The agreement premise holds at the guess, which `u⃗, o_β ▷ m` holds of
with the guess as witness, so at every `η` where the bits fit on the tape,
`deduceAdv g (u⃗, o₁) v ≤ deduceAdv g (u⃗, o₂) v + 2^⌈log₂ q(η)⌉ · Pr[o₁(m) ≠ o₂(m)]`, and long
tapes make that hold at every large `η`. Pc-Oracle follows from the double rule at `β = 2`, as
[CCS26] derives it: where `u⃗, o′ ▷ m'`, Ineq gives `m ≠ m'` overwhelmingly from `u⃗, o′ ⊬ m`, and
`o` and `o′` agree away from `m` (L29).

**G.PRF: the compiled reading and handler composition.** [CCS26, App. C.3]'s PRF reduction
evaluates the terms of the vector and the message itself, sending each hash with the key to the PRF
oracle. Here those terms are written with explicit calls `o_h^k(t)` (`OTerm`, over PolyFun's sum of
the local signature and a call constructor) and closed up by replacing each call with `h(t, k)`
(`PRFSymbols.close`). The reduction's evaluator is PolyFun's call-by-value reading `Term.denoteCBV`
at one interpretation, `PRFSymbols.cbvInterp`: a term becomes a free program over the honest
coins, the attacker tape and the hash oracle, with arrows read as Kleisli arrows, and nothing in the
compiler is specific to a term. Its adequacy is PolyFun's fundamental lemma
`Term.denoteCBV_related` at a logical relation (`PRFSymbols.CRel`: equality at Boolean and base
types, and at arrows "related arguments give related runs"), whose one obligation,
`CBVInterpretation.RelatedOn`, is checked head by head on the `⊢pptm` fragment (L25). With the
ordinary reading paired with a proposition about the call arguments (`PRFSymbols.guardInterp`), the
same lemma shows that the run hashes only values of call arguments (`PRFSymbols.denoteCBV_guard`,
over VCVio's `runLog`), which is what `ψ_msg` gives a reduction (L3, L26). The reductions
`PRFSymbols.hashReduction` and `PRFSymbols.freshReduction` are built by handler composition: VCVio's
`simulateQ` of a handler (`PRFSymbols.fwd`) answers coins and the tape from tapes the reduction
draws and forwards hash queries to the PRF oracle, logging them (`withQueryLog`), and the
distinguisher's machine runs inside the reduction (`Machine.simulate`); its inputs are answered
from values, so its run fuses into the reduction (`Machine.simulate_ofVals`). The proof has three
hops. In the real world a forwarded run is the run with the key's answers
(`simulateQ_prfRealQueryImpl_fwd`), and writing the PRF key and the challenge into the honest tape
gives a uniform tape (`SampleableType.prEvent_uniformSample_prod_update_update`). In the ideal world
the two reductions agree, since the lazily sampled function is uncached at a message the run did
not hash (`prEvent_prfIdealExperiment_hashReduction`). The guard that the message was not hashed
costs at most `Pr[¬ψ_msg]`. At every `η`,
`advantage A (u⃗, h(m, k)) (u⃗, n) η ≤ prfAdv (hashReduction η u m A) + prfAdv (freshReduction η u m A) + Pr[ψ_msg = false]`
(`PRFSymbols.advantage_le`, L6). PRF-Simple is derived as [CCS26, p. 17] derives it: G.PRF at the
vector `u⃗, v`, Perm (`swapLast`), FreshL and Rw-Equiv (`Valid.nonDed_prf`).

**PRF.R and PRF.L-sec: the hash oracle as an input.** [CCS26, Fig. 4] puts the hash oracle
`o_h^k = λx. h(x, k)` (`PRFSymbols.hashOracle`) on the left. A reduction runs the attacker's
machine inside a VCVio adversary and answers its oracle input by Kleisli-applying the compiled
`λx. call x` (`PRFSymbols.arrowIn`, `PRFSymbols.kapp`): one hash query per oracle query, forwarded
to the PRF oracle. With the keyed hash's answers the run is the machine's run on `h(·, k)`
(`Machine.evalWithAnswerFn_simulate`), and the attacker's hashes are its oracle queries
(`PRFSymbols.exists_firstArgs_of_hashed`, from VCVio's `mem_runLog_simulateQ`) (L30). PRF.R's
reductions `PRFSymbols.rightReduction`, one per candidate among the message `m` and the arguments
of its calls, run the vector, the attacker and the candidate, and query the PRF oracle at the
candidate's value last. Some candidate has `m`'s value and is not hashed by its own run
(`PRFSymbols.exists_unhashed`), and in the ideal world its challenge is a fresh draw, which the
attacker's output hits with probability at most `2^{-cη}`; the attacker's queries at `m` are
bounded by Rw-Oracle's guess against the premise. At every large `η`,
`deduceAdv g (u⃗, o_h^k) (h(m, k)) η ≤ Pr[ψ_msg(u⃗) = false] +
2^⌈log₂ q(η)⌉ · deduceAdv (rwGuess g) (u⃗, o_h^k) m η +
Σ_t (prfAdv (rightReduction η hmg hh u t g) + 2^{-cη})`
(`PRFSymbols.rightAdvantage_le`, L31). PRF.L-sec's reductions `PRFSymbols.leftReduction` and
`PRFSymbols.leftFreshReduction` intercept the attacker's oracle at the message and answer it by the
challenge (`PRFSymbols.interceptIn`), so their ideal worlds agree as distributions (VCVio's
`OracleSpec.fst_map_run_simulateQ_romImpl_eq_of_allQueriesSatisfy`). In the second's real world the
reprogrammed oracle runs as the keyed hash until the message is queried
(`Machine.run_cons_eq_of_firstArgs`, `Machine.runLog_cons_eq_of_firstArgs`), and its fresh draw is
read from a block of the attacker tape above the read bounds (`prEvent_coin_eq_coinAt`), which makes
the attacker FreshL's reduction against the premise, and its queries at the message the guess
against `C_sec`. At every large `η` the attacker's success against `u⃗, o_h^k, h(m, k) ⊢ v` is at
most `Pr[ψ_msg(u⃗, v, m) = false]`, the two PRF advantages, the success of FreshL's reduction
against `u⃗, o_h^k ⊢ v`, and `2^⌈log₂ q(η)⌉` times the success of the guess against
`u⃗, o_h^k ⊢ m` (`PRFSymbols.leftAdvantage_le`, L32).

**Freshness.** The honest tape has one coin per name and index, and a name reads only the coins
of its own slots, so freshness of names is syntactic. `FTerm.AvoidsNames N t` says that no head of
`t`, in the sense of PolyFun's `Term.heads`, is the constructor of a name in `N`. It is a fold over
the term, decidable for a decidable `N`, so `decide` checks it on concrete terms; and PolyFun's
`Term.denote_update_eq` gives that such a term ignores every coordinate of the honest tape that
belongs to a name in `N` (`FTerm.denote_update_eq_of_avoidsNames`), with no induction over terms.
The encryption rule's side conditions are of this kind, and so are G.PRF's freshness of its name and
FreshR's and FreshL's, for closed terms (L22): a free variable ranges over all random variables, which may read the name.
For a closed term, `FTerm.AvoidsNames.freshAt` gives the semantic statement the proofs use, that
its random variable agrees at two honest tapes that differ only at the name's coordinate
(`Model.FreshAt`). Not using a name at all is stronger than not reading the coordinate a given
occurrence reads. FreshR also has a form whose freshness premise is that semantic statement, under
the hypotheses (`Valid.nonDed_freshR_of_freshAt`): an oracle punctured back to the identity uses
the name it punctures and reads none, and the check of Pc-Oracle uses it there.

## 7. Derivations as data

`Derivation D enc prf R₀ Θ F` is an inductive type with one constructor per rule, indexed by the
context, the hypotheses and the conclusion; local sequents are unfolded to the global sequents they
stand for. `Derivation.sound R C` maps every derivation to `Valid R C Θ F`, one rule lemma per
constructor, for every model restriction contained in `R₀` and every class of machines. Derivations
are data: Lean functions can build them, for example by recursion on a protocol's trace
(`Chain.chainPFS`), and the kernel checks them. A rule with a semantic side condition takes it as a
premise of its constructor.

The encryption rule is a constructor at the instances that the parameter `enc` admits. Its syntactic
side conditions (`EncInstance.Syntactic`: distinct key and coin names, which the messages and the
context do not use) are a premise of the constructor, which `decide` discharges on concrete
instances; `Derivation.sound` takes the semantic hypotheses of each admitted instance
(`EncInstance.Holds`: equal message lengths in every admitted model, and one-time IND-CPA for the
reductions of the admitted machines). With `enc` empty, derivations use the other rules only.
[BC14]'s If1 is a constructor although the case split proves it: deriving it would rewrite
`if c' then z else z` to `z`, and the fragment has no rule proving that local equality.

G.PRF is a constructor in the same way, at the instances that the parameter `prf` admits
(`PRFRule`, `Derivation.equivPRF`). Its syntactic side conditions (`PRFInstance.Syntactic`: `ψ_key`,
`⊢pptm`, first order, Boolean or base types, and a name that is not the key and is fresh in the
closed-up terms) and its `[ψ_msg]` are premises; `decide` discharges the former on concrete
instances. `Derivation.sound` takes the semantic hypotheses of each admitted instance
(`PRFRule.Holds`: uniform names of the hash type in every admitted model, and the PRF assumption
for the two named reductions of each admitted machine). PRF-Simple is not a constructor: it is
derived from G.PRF, Perm, FreshL and Rw-Equiv (`Derivation.nonDedPRF`), as [CCS26] derives it.
PRF.R and PRF.L-sec are constructors at the instances `prf` admits too (`PRFRule.right`,
`PRFRule.left`; `Derivation.nonDedPRFR`, `Derivation.nonDedPRFLSec`). Their syntactic side
conditions (`PRFRInstance.Syntactic`, `PRFLInstance.Syntactic`, the latter decidable) and their
`[ψ_msg]` are premises, and so are, as for FreshL, that `R₀` gives uniform names of the hash type,
long tapes and polynomial bit blocks for messages (and for hashes, PRF.L-sec), with the read bounds
of their terms. `PRFRule.Holds` is the PRF assumption on their named reductions.

The parameter `R₀` is the restriction on models that a derivation's rules assume, and
`Derivation.sound` holds over every restriction contained in it. FreshL is sound only over models
with long attacker tapes, so its constructor takes as premises that `R₀` gives long tapes and
polynomial bit blocks for the name's type, and that the terms read the attacker tape below a
polynomial in every model of `R₀` and of the hypotheses. Rw-Oracle and Pc-Oracle draw their
guess from the attacker tape in the same way, so their constructors take the same premises, with
polynomial bit blocks for the oracles' argument type. Pc-Oracle is a constructor of its own:
[CCS26] derives it from the double Rw-Oracle by concluding the agreement premise with Ineq under
the hypothesis `u⃗, o′ ▷ m`, which the fragment has no rule to introduce. `boxValid` concludes `[φ]`
for a local formula true at every tape of every model of `R₀`, which is how equations that `R₀`
imposes on honest symbols are used. A derivation that uses none of these takes `R₀` to be every
model. FreshR's and FreshL's freshness premises are syntactic, and `decide` discharges them on
concrete terms; Rw-Equiv, Rw-Oracle and Pc-Oracle take the ground types they need as premises.
`Derivation.boxOfMap` combines `boxValid` and `boxMP` to conclude `[χ]` from boxes indexed by a
list when `χ` follows locally from them.

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
| Neg1, Neg2 | [CCS26, Fig. 3] | `Valid.not_ded`, `Valid.not_nonDed` | `Derivation.notDed`, `Derivation.notNonDed` |
| Ineq | [CCS26, Fig. 3] | `Valid.box_not_eq` | `Derivation.boxNotEq` |
| Trans | [CCS26, Fig. 3] | `Valid.ded_trans` | `Derivation.dedTrans` |
| WeakL, WeakR | [CCS26, Fig. 3] | `Valid.nonDed_weakL`, `Valid.nonDed_weakR` | `Derivation.nonDedWeakL`, `Derivation.nonDedWeakR` |
| Rw-Equiv, for a right side of Boolean or base type | [CCS26, Fig. 3] | `Valid.nonDed_rwEquiv` | `Derivation.nonDedRwEquiv` |
| `u⃗ ▷ f(u⃗)` from `adv(f)` | [CCS26, §3.1] | `Valid.ded_apps` | `Derivation.dedApps` |
| Deducing an entry, an honest symbol, an application, a rewritten term | [CCS26, §2.3] | `Valid.ded_input`, `Valid.ded_fn`, `Valid.ded_app`, `Valid.ded_rewrite` | `Derivation.dedInput`, `Derivation.dedFn`, `Derivation.dedApp`, `Derivation.dedRewrite` |
| Local validity, modus ponens under `[·]` | local reasoning, read semantically | `Valid.box_valid`, `Valid.box_mp` | `Derivation.boxValid`, `Derivation.boxMP`; combined over a list: `Derivation.boxOfMap` |
| FreshR | [CCS26, Fig. 11] | `Valid.nonDed_freshR`; with a semantic freshness premise, `Valid.nonDed_freshR_of_freshAt` | `Derivation.nonDedFreshR` |
| FreshL | [CCS26, Fig. 11, App. C.2] | `Valid.nonDed_freshL` | `Derivation.nonDedFreshL` |
| Rw-Oracle, as the double rule; in the form of Fig. 3 | [CCS26, Fig. 3, App. C.1] | `Valid.nonDed_rwOracle_of`; `Valid.nonDed_rwOracle` | `Derivation.nonDedRwOracle` |
| Pc-Oracle | [CCS26, Fig. 3, App. C.1] | `Valid.nonDed_pcOracle` | `Derivation.nonDedPcOracle` |
| G.PRF, without an oracle on the left | [LICS23] (G.PRF); [CCS26, Fig. 11, App. C.3] | `Valid.equiv_prf` | `Derivation.equivPRF` |
| PRF-Simple | [CCS26, Fig. 4, Fig. 11, p. 17] | `Valid.nonDed_prf` | derived: `Derivation.nonDedPRF` |
| PRF.R, with the hash oracle on the left | [CCS26, Fig. 4, App. C.3.2] | `Valid.nonDed_prfR` | `Derivation.nonDedPRFR` |
| PRF.L-sec, in the form of §2.3 | [CCS26, §2.3, Fig. 4, Remark 1, App. C.3.1] | `Valid.nonDed_prfLSec` | `Derivation.nonDedPRFLSec` |

Results derived with these rules:

| Result | Source | Validity | Derivation |
|---|---|---|---|
| Forward secrecy of the toy ratchet, `frame(τ′) ⊬ ck(τ)` at every safe `τ`, for each trace given as a Lean value | [CCS26, §2, Fig. 1–2] | `Chain.chainPFS_sound`, `Chain.pfsFrame_sound` | `Chain.chainPFS`, `Chain.pfsFrame`: FreshR and PRF.R at the updates (`Chain.secrecyBase`), the deduction rules for the frame (`Chain.sim`), PRF.L-sec at `Corrupt` with `ψ_msg` from the NoCollision hypotheses and Ineq (`Chain.psiL`), WeakL |

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
  unrestricted IND-CPA game;
- `Test/SecrecyExamples.lean`: the derivation `h(h(k)) ⊬ n` from `adv(h)` with its soundness, in a
  model where `msg` is large; `⊬` is not transitive; Neg1, Neg2, Ineq, Rw-Equiv and WeakR each
  used, with checks that Neg1, Ineq, Rw-Equiv and WeakR need a premise; the deductions, local
  validity and modus ponens under `[·]` used in a derivation of `h(h(k)) ▷ k`; FreshR fails
  without `large`, and FreshL without freshness;
- `Test/FreshLExamples.lean`: a model with tapes of `2^η` bits, where every hypothesis of FreshL
  holds against `AdvClass.all` and a worked derivation ends with FreshL; with the name not fresh,
  the conclusion fails;
- `Test/FreshLCountermodel.lean`: FreshL fails without long tapes. In a model with an empty
  attacker tape, against the class generated by the closure fields, the guessing machine among
  them, its premise holds and its conclusion fails while its other hypotheses hold;
- `Test/OracleExamples.lean`: in the model with long tapes, every hypothesis of Rw-Oracle holds
  jointly at `β = 2` for an oracle that hides a secret behind a secret point, with a conclusion
  that FreshR does not give; Rw-Oracle in the form of Fig. 3; the agreement premise is needed, for
  an oracle that hides the secret behind the attacker's own message; and a worked Pc-Oracle;
- `Test/PRFExamples.lean`: in a model whose hash is a perfect PRF, the compiled program of
  `o_h^k(c)` makes exactly one hash query, adequacy holds at a term with a name and a call, and
  outside `⊢pptm` the compiled reading of a local quantifier disagrees with the term; every
  hypothesis of G.PRF and of a worked PRF-Simple holds jointly against `AdvClass.all`, with the
  syntactic side conditions checked by `decide`; and G.PRF fails without `ψ_msg` and without
  `ψ_key`, each while every other hypothesis holds;
- `Test/PRFOracleExamples.lean`: in the same model, against all machines, every hypothesis of two
  PRF.R steps holds jointly, deriving `o_h^k ⊬ h(h(s, k), k)`, and so does every hypothesis of a
  PRF.R step followed by PRF.L-sec, deriving `o_h^k, h(r, k) ⊬ h(s, k)`; neither right side is a
  name, so FreshR does not give them. PRF.L-sec fails without `ψ_msg`, PRF.R without its premise
  (the attacker queries its oracle at a constant message) and PRF.L-sec without its premise, each
  while every other hypothesis holds.
- `Test/ChainModel.lean`: in a model whose hash is a perfect PRF, whose pair keeps its first
  component and whose frames are all bitstrings, against all machines, every hypothesis of
  `Chain.chainPFS_sound` holds jointly: the model conditions, the PRF assumption of every PRF.R and
  PRF.L-sec instance, `adv(att)`, and the NoCollision lemmas, which fail with probability at most
  `n² · 2^{-η}` for `n` updates since the keys are iterates of a uniform function table (VCVio's
  `OracleComp.prEvent_iterate_collision_le`). So every safe key is secret from the last frame of
  every trace there. The derivation gives no concrete bound on the attacker's success, since its
  conclusion is asymptotic. With every hypothesis holding, the key output at `Corrupt` is deducible
  from the frame that outputs it, so the safety condition is needed.

## 9. Obligations

Each row is a point where the papers leave something informal or where the formalization makes a
modelling choice. A row is closed only by a Lean theorem, or a countermodel, named in its last
column. The ids are stable: a row keeps its id when rows are added, so the ids here are not
contiguous. Every name in the last column is in the namespace `Interop.Squirrel`.

| Id | Kind | Source anchor | Obligation | Status | Lean anchor |
|---|---|---|---|---|---|
| L2 | gap | [CCS26] Fig. 3, App. C.1 (pp. 15–16) | Rw-Oracle has no premise bounding the size of oracle answers, yet its proof assumes them polynomial: the paper's `A_j` simulates `A`, so it copies every answer onto `A`'s tape and its time depends on their size. Here the reduction `AdvMachine.rwGuess` never computes `o₁` or `o₂`: it runs the attacker machine through a handler that forwards each oracle query to its own oracle input and keeps the query's argument (`Machine.guess`). Answers are typed values that the handler passes on, so the rule needs no premise on their size; the efficiency obligation is the closure field `AdvClass.guess_mem`, whose polynomial-time counterpart is VCVio's handler closure with a logging handler of constant cost per query. The arguments the guess keeps were written by the attacker machine, so its time bounds them. A class whose machines pay for copying answers would meet `guess_mem` only under a premise on their size. | closed (efficiency in the class field) | `AdvClass.guess_mem`, `Machine.guess`, `AdvMachine.rwGuess`, `AdvClass.NonDed.rwOracle`, `Valid.nonDed_rwOracle_of`, `Valid.nonDed_rwOracle` |
| L3 | informal | [CCS26] Fig. 11, App. C.3; [LICS23] p. 29 (G.PRF), Fig. 1 (p. 4) | The PRF side conditions `ψ_key` and `ψ_msg` are not defined formally. Here the vector and the message are terms with explicit calls `o_h^k(t)` (`OTerm`, over the sum of the local signature and a call constructor), closed up into the logic's terms by replacing each call by `h(t, k)` (`PRFSymbols.close`, a fold). **ψ_key** is a condition on the heads of the terms with calls (PolyFun's `Term.heads`), decidable when names have decidable equality: no head is the key name (`PRFSymbols.KeyFree`), so in the closed-up terms the key occurs only as the key of `h`. What it gives is that the reading ignores every coordinate of the key name (`PRFSymbols.ointerp_eq_of_keyFree`, from PolyFun's `Term.denote_congr_of_heads_subset`). LICS23 also admits key occurrences `k t₀` at other indices with `t₀ ≠ t`; here the key name occurs nowhere else, which is stronger. **ψ_msg** is a generated local formula: over the arguments `t′` of the calls of `u⃗` and `m` (`PRFSymbols.calls`, a fold), the conjunction of `t′ ≠ m` (`PRFSymbols.psiMsg`). The challenge is not among the calls. PRF.R's `ψ_msg` ranges over the calls of `u⃗` only (`PRFSymbols.psiMsgVec`) and PRF.L-sec's over those of `u⃗`, `v` and `m` (L26). The restriction to first-order terms and the dropped conditions of conditionals are L26. Each is shown necessary by a countermodel in which every other hypothesis of G.PRF holds, and `ψ_msg` by one in which every other hypothesis of PRF.L-sec holds. | closed (this fragment) | `PRFSymbols.close`, `PRFSymbols.KeyFree`, `PRFSymbols.ointerp_eq_of_keyFree`, `PRFSymbols.psiMsg`, `PRFSymbols.psiMsg_eq_true_iff`, `PRFSymbols.psiMsgVec`, `PRFSymbols.denoteCBV_guard`, `PRFExamples.gprf_needs_psiMsg`, `PRFExamples.gprf_needs_psiKey`, `PRFOracleExamples.prfLSec_needs_psiMsg` |
| L6 | gap | [SP21] App. C; [LICS23] p. 29 (G.PRF); [CCS26] Fig. 4, Fig. 11, App. C.3 (pp. 7, 17–19) | The rules lifted from the base logic (CCA1, ENC-KP, DDH, PRF, INT-CTXT) have no detailed proofs. G.PRF without an oracle on the left, `u⃗, h(m, k) ∼ u⃗, n`, is proved from VCVio's PRF game (`prfAdvantage`) for the fragment of L25 and L26. Two named reductions, `PRFSymbols.hashReduction` and `PRFSymbols.freshReduction`, run the compiled vector and message with their hash queries forwarded to the PRF oracle; at every `η` the advantage is at most their two PRF advantages plus `Pr[¬ψ_msg]`. The PRF assumption is a hypothesis on these two reductions of each admitted machine, never on every adversary of a type. The hops: real to ideal for each reduction; in the ideal world the two agree, since the lazily sampled random function is uncached at a message the run did not hash; and the guard that the message was not hashed costs at most `Pr[¬ψ_msg]`, because the compiled run hashes only the values of call arguments. The model condition is that names of the hash type are uniform (`Model.UniformSampler`), so that `n` is distributed as a random function's value; the name `n` is not the key and is fresh in the closed-up terms, syntactically (L22). PRF-Simple is derived from G.PRF, Perm, FreshL and Rw-Equiv as CCS26 derives it (p. 17). The hypotheses are jointly satisfiable with `AdvClass.all` in a model whose hash is a perfect PRF. PRF.R, with the oracle `o_h^k` on the left, is proved by the reductions `PRFSymbols.rightReduction`, one per candidate among the message and the arguments of its calls (L30, L31): at every large `η` the attacker's success is at most `Pr[¬ψ_msg(u⃗)]`, plus `2^⌈log₂ q(η)⌉` times the success of the uniform guess against the premise `u⃗, o_h^k ⊢ m`, plus a PRF advantage and `2^{-cη}` per candidate. Its hypotheses are jointly satisfiable in the perfect-PRF model, where two PRF.R steps derive `o_h^k ⊬ h(h(s, k), k)`, which FreshR does not give, and its premise is needed. PRF.L-sec, in the form of CCS26 §2.3 (L32), is proved by the reductions `PRFSymbols.leftReduction` and `PRFSymbols.leftFreshReduction`: at every large `η` the attacker's success is at most `Pr[¬ψ_msg(u⃗, v, m)]`, plus the two PRF advantages, plus the success against the premise of FreshL's reduction of the attacker, plus `2^⌈log₂ q(η)⌉` times the success against `C_sec` of the guess of its oracle queries. Its hypotheses are jointly satisfiable in the perfect-PRF model after a PRF.R step, and `ψ_msg` and the premise are needed. In both the PRF assumption is a hypothesis on the named reductions of each admitted machine. The toy ratchet's derivation (`Chain.chainPFS`) uses PRF.R at each update and PRF.L-sec at the corruption, and their hypotheses hold jointly with the rest in `ChainModel.cmodel`. Still open: CCA1 with decryption, ENC-KP, DDH, INT-CTXT, PRF.L-eq and PRF.L-⊤ (L32). | open | `Valid.nonDed_prfR`, `PRFSymbols.rightAdvantage_le`, `PRFSymbols.rightReduction`, `Derivation.nonDedPRFR`, `PRFOracleExamples.valid_chainWorked`, `PRFOracleExamples.prfR_needs_premise`, `Valid.nonDed_prfLSec`, `PRFSymbols.leftAdvantage_le`, `PRFSymbols.leftReduction`, `PRFSymbols.leftFreshReduction`, `Derivation.nonDedPRFLSec`, `PRFOracleExamples.valid_leftWorked`, `PRFOracleExamples.prfLSec_needs_premise`, `Valid.equiv_prf`, `PRFSymbols.advantage_le`, `PRFSymbols.hashReduction`, `PRFSymbols.freshReduction`, `PRFSymbols.prEvent_prfIdealExperiment_hashReduction`, `Model.UniformSampler`, `Valid.nonDed_prf`, `Derivation.equivPRF`, `Derivation.nonDedPRF`, `PRFExamples.valid_gprf`, `PRFExamples.valid_prfWorked`, `Chain.chainPFS`, `ChainModel.valid_chainPFS` |
| L7 | gap | [LICS23] Fig. 8; [BC14] Prop. 2 | LICS23 gives no proof of G.Case-Study:ITE and refers to BC14, whose Prop. 2 proves only If1, with one condition and one context on both sides. Its machines flip a coin when the condition fails, and their success probability, written `1/4 + p`, holds only when the condition is true with probability one half; the error cancels because the condition is shared, and would not with two conditions. The case split is proved here with two conditions, by two named reductions that return `false` when the condition fails, with the advantage at most the sum of the premises' advantages at every `η` (factor one; BC14's factor two comes from naming one of the two machines). If1 is its instance with both right-hand branches equal. A countermodel shows that each premise must keep the condition beside its branch. | closed (case split) | `advantage_cons_cond_le`, `Valid.equiv_caseStudy`, `Valid.equiv_if1`, `CaseStudy.caseStudy_needs_condition` |
| L10 | choice | [LICS23] p. 5, Fig. 2 (p. 7) | Adversaries read the shared attacker tape `ρa` in the papers, while VCVio adversaries draw fresh coins. Here `ρa` is a uniform bitstring of a length the model chooses (`Model.TapeA`), and machines read it bit by bit through the tape interface (`tapeSpec`), as LICS23's machines read their randomness tape; attacker symbols read the same tape. Relating these machines to VCVio adversaries with fresh coins is open. | open | `Model.TapeA`, `tapeSpec`, `Machine.run` |
| L11 | choice | [LICS23] p. 7; [CSF24] App. A; [CCS26] §3.1 (p. 6) | `∼` at arbitrary order (LICS23) versus order at most 1 for `∼` and at most 2 for `adv` (CSF24, CCS26). The fragment of CSF24 and CCS26 is adopted and made syntactic: the global constructors `adv τs β` and `equiv τs` carry proofs of `Ty.AdvOrder τs β` (the term `τ₁ → … → τₙ → β` has order at most 2) and `Ty.IndistOrder τs` (entries of order at most 1), so an atom outside the fragment cannot be written. The semantics is defined at every type. Rw-Oracle and Pc-Oracle use `adv` at order two: the attacker machine has an input of order one, the oracle, which it queries, and the guess keeps the arguments of those queries (L2, L27). | closed (adopted fragment) | `GlobalOp`, `Ty.AdvOrder`, `Ty.IndistOrder`, `Valid.nonDed_rwOracle_of`, `OracleExamples.valid_rwOracleWorked` |
| L12 | choice | [LICS23] §II-B (pp. 5–6) | Names read the honest tape, a product with one uniform bit block per name and index (`Model.Coin`, `coinLen η τ` bits); a name reads its own block and runs the sampler of its type on it, and names of one type share a sampler, so independence and identical distribution are structural, and a machine reading as many bits of its own tape and running the sampler draws a name's distribution. LICS23 (p. 6) notes that a name needs finitely many bits of the honest tape and requires names to be samplings computable in polynomial time. Both halves are stated where the rules use them: polynomial bit blocks are the model condition `Model.PolyCoins`, a hypothesis of FreshL, Rw-Oracle and Pc-Oracle on the model restriction; polynomial-time samplers are the closure field `AdvClass.sampler_mem`, which admits the machine reading `coinLen η b` bits of the attacker tape and running the sampler (`Machine.sampler`), a compatibility condition between model and class like `fn_mem` for honest symbols. Neither is imposed on models in general, and polynomial time itself is not imposed on the class (L14). | closed (stated as conditions) | `Model.TapeH`, `Model.Coin`, `Model.name`, `Model.PolyCoins`, `Machine.sampler`, `Machine.run_sampler`, `AdvClass.sampler_mem` |
| L13 | choice | [LICS23] Fig. 2 | `const t` at arrow types is read as a logical relation (`Ty.Same`). LICS23 asks for a value in `⋂_η ⟦τ⟧_η`; the two agree at base types and at arrows from fixed types, and differ when the domain varies with `η`. | open | `Ty.Same`, `RV.IsConst` |
| L14 | choice | [LICS23] §II-C.1, §II-C.2, Fig. 2 (p. 7) | The machines of `adv` and `∼` are free programs (`OracleComp`) over the sum of a tape interface and an input interface, run by fixed answers. LICS23's machines receive base values as bitstring encodings on input tapes and functions through handles on a query tape; here every input is an oracle that receives and returns typed values, a base input is queried with no arguments, and a query supplies all of a function's arguments (no handles for partial applications, which inputs of order at most 1 do not need). The class `AdvClass` is a predicate on machines, closed under the constructions that the rules' reductions use (section 4), and a parameter of validity: polynomial time is not imposed. `AdvClass.all`, the machines with polynomial read and query bounds, is the class of the satisfiability checks. | open | `Machine`, `Machine.ReadsBelow`, `Machine.QueryBound`, `AdvClass`, `AdvClass.all` |
| L15 | choice | [LICS23] §II-A, §II-B | LICS23's declared variables are split into constructors (names, honest symbols with tape-independent values, attacker symbols reading `ρa`, `=_τ`, `∀_τ`, `∃_τ`) and free variables, which range over all random variables. | open | `Decl`, `localSig` |
| L16 | choice | [BC14] (α-renaming of names); [LICS23] §II-B.2 | Renaming names in a closed vector is sound along any type-preserving bijection of names, in every model: the renaming is the permutation `Model.tapePerm` of the honest tape's coordinates. The residue is the restriction to closed vectors, which LICS23's rule shares (free variables range over all random variables, which may read the tape). | closed | `Model.renamesNames`, `Valid.equiv_renameNames_of_equiv`, `Derivation.equivRenameNames`, `TwoTimePad.valid_swap` |
| L17 | gap | [BC14] §7 (Fig. 2, EncCCA1; Prop. 3); [LICS23] Prop. 19 (G.CCA1) | Soundness of the encryption rule when the secret key is never used to decrypt: `pk(nk), enc(m₀; r, pk(nk)), u⃗ ∼ pk(nk), enc(m₁; r, pk(nk)), u⃗`, in left-or-right form. The key and coin names are distinct; the messages and the context have the public key free and are closed by substituting `pk(nk)`, and they use neither the key name nor the coin name (syntactic side conditions, L22); in every admitted model the two messages have equal length at every tape (a restriction on models). The length condition is BC14's guard `EQL(u, u′)` holding surely, as in LICS23's G.CCA1, where `zero (len m)` has the length of `m` in every model. The assumption is one-time IND-CPA (`IND_CPA_OneTime_Advantage` at `ProbCompRuntime.probComp`) for the image of the class under the named reduction `EncSymbols.encReduction`, which submits only pairs of equal length (it is admissible for the leakage `lenOf`); at every `η` the two advantages are equal. A scheme that leaks lengths meets every hypothesis, though it fails VCVio's unrestricted game. Countermodels show that the IND-CPA hypothesis, the distinct names and the freshness of the coins in the context are each needed. Still open: decryption (IND-CCA1), BC14's guard as a conditional in the conclusion for messages whose lengths differ on some tapes, and the real-or-zero form. | closed (this fragment) | `Valid.equiv_enc`, `EncSymbols.advantage_challenge`, `EncSymbols.encReduction_isAdmissible`, `WorkedEnc.workedDerivation_sound`, `WorkedEnc.valid_worked_lpad`, `WorkedEnc.lpad_advantage_unequalAdv`, `EncExamples.not_valid_enc_leaky`, `WorkedEnc.not_valid_leak`, `EncExamples.not_valid_enc_keyIsCoin`, `EncExamples.not_valid_enc_coinReused` |
| L18 | choice | [CCS26] §3.1 (p. 6), Fig. 3 (p. 7) | `u ⊬ v` and `u ▷ v` are global formulas built from `∀̃`/`∃̃`, `adv`, `⇒̃`/`∧̃` and `[·]`, with no new primitive (`Form.nonDed`, `Form.ded`), restricted to entries and right side of order at most one (`Ty.SecrecyOrder`), so that the attacker function has order at most two. The logic has no product types, so a tuple on the left is a vector and the attacker function is curried (`Ty.arrows`); the right side is one term, and a term in the middle of Trans or WeakL, being on the right of a `▷`, is a vector of one. Each rule of Fig. 3 is proved and used in a kernel-checked check, Rw-Oracle and Pc-Oracle under the conditions of L29, and Neg1, Ineq, Rw-Equiv, WeakR and Rw-Oracle have checks that a premise is needed. Deductions from the entries of the vector, honest symbols, application and rewriting are rules of their own, and local reasoning is read semantically (`Valid.box_valid`, `Valid.box_mp`, combined over a list of facts by `Derivation.boxOfMap`) rather than as a calculus. | closed (this fragment) | `Form.nonDed`, `Form.ded`, `Form.holds_nonDed`, `Form.holds_ded`, `Ty.SecrecyOrder.advOrder`, `Valid.not_ded`, `Valid.not_nonDed`, `Valid.box_not_eq`, `Valid.ded_trans`, `Valid.nonDed_weakL`, `Valid.nonDed_weakR`, `Valid.ded_apps`, `Valid.ded_input`, `Valid.ded_fn`, `Valid.ded_app`, `Valid.ded_rewrite`, `SecrecyExamples.workedDerivation_sound`, `SecrecyExamples.nonDed_not_trans`, `SecrecyExamples.valid_neg1`, `SecrecyExamples.valid_neg2`, `SecrecyExamples.valid_ineq`, `SecrecyExamples.valid_rwEquiv`, `SecrecyExamples.valid_weakR`, `SecrecyExamples.neg1_needs_nonDed`, `SecrecyExamples.ineq_needs_nonDed`, `SecrecyExamples.rwEquiv_needs_equiv`, `SecrecyExamples.valid_ded_k_app_hk`, `SecrecyExamples.rewriteDerivation_sound`, `Derivation.boxOfMap`, `Valid.nonDed_rwOracle_of`, `Valid.nonDed_pcOracle`, `OracleExamples.rwOracle_needs_agree` |
| L19 | choice | [LICS23] App. A (label `large`), §II-B.1 | `large` is LICS23's bound `Pr_ρh[⟦n⟧(η, a)(ρh) = b] ≤ 2^{-c·η}` for some real `c > 0`, read on the sampler that names of the type share. LICS23 lifts labels to compound types "in the natural way" without saying how `large` lifts; here Booleans and arrow types are not `large`. A base type labelled `finite`, `fixed` and `large` has no model, so the checks that use the trivial model assume no `large` base type. FreshR uses the label, and is unsound without it: a Boolean name, fresh in the empty vector, is guessed with probability one half. | open | `Model.IsLarge`, `Ty.HasLabel`, `Model.isLarge_of_hasLabel`, `Model.trivial_respectsLabels`, `Valid.nonDed_freshR`, `SecrecyExamples.model_isLarge`, `SecrecyExamples.freshR_needs_large` |
| L20 | gap | [CCS26] Fig. 11, App. C.2 and footnote 2 (pp. 16–17); [LICS23] §II-A.3, §II-C.1, p. 17 | FreshL (`u ⊬ v ⟹ u, n ⊬ v`, `n` fresh in `u, v`) is proved in App. C.2 through a function `f′` that "simulates the sampling of `n_fresh` from the adversarial randomness and then runs `f`". Footnote 2 (p. 17) makes room for that randomness by extending the model's attacker tape and applying the premise "in the extended model", "since the secrecy property `u ⊬ v` is assumed to hold in any model". The premise is `E; Θ ⊢ u ⊬ v`, which holds only in models of `Θ`, and the footnote does not show that `Θ` holds in the extended model. The formalization extends no model. The attacker tape is a bitstring of model-chosen length; the reduction `AdvMachine.freshL` answers the fresh name's input of the attacker machine (`Machine.subst`) by the sampler of its type run on the bits `[p(η), p(η) + coinLen η b)` of the same tape (`Machine.shift`, `Machine.sampler`), with `p` the sum of the read bounds of the machine (`AdvClass.readBound_mem`) and of the terms; long tapes (`Model.LongTapes`, L23), a hypothesis on the model restriction, give those bits at every large `η`. At each such `η` the reduction's success against `u ⊢ v` equals the machine's against `u, n ⊢ v`, by one bijection of the tapes that swaps that block with the name's honest coordinate. The premise is used in the model where the conclusion is evaluated, so the question whether `Θ` holds in an extended model does not arise. The side conditions: the terms are closed and do not use the name (`FTerm.AvoidsNames`, L22), and they read the attacker tape below a polynomial (`FTerm.ReadsPoly`, discharged structurally; L24). The hypotheses are jointly satisfiable with `AdvClass.all` in a model with tapes of `2^η` bits, where a worked derivation ends with FreshL; FreshL fails without long tapes, against the class generated by the closure fields, and fails without freshness. Derivations carry the restriction `R₀` that their rules assume, and FreshL's constructor requires long tapes and polynomial bit blocks in `R₀`. | closed (this fragment) | `deduceAdv_freshL_eq`, `AdvClass.NonDed.freshL`, `Valid.nonDed_freshL`, `AdvMachine.freshL`, `AdvClass.freshL_mem`, `Derivation.nonDedFreshL`, `Derivation.sound`, `FreshLExamples.valid_freshLWorked`, `FreshLExamples.not_valid_freshL_n`, `FreshLCountermodel.freshL_needs_longTapes`, `SecrecyExamples.freshL_needs_freshness` |
| L21 | choice | [CCS26] Fig. 3 (Rw-Equiv) | Rw-Equiv is proved for a right side of Boolean or base type. Its distinguisher tests `f(u) = v`, which no machine does at an arrow type, and the class is asked for the equality test only at these types. | open | `Valid.nonDed_rwEquiv`, `Machine.deduce`, `AdvClass.deduce_mem`, `AdvClass.eqTest_mem` |
| L22 | choice | [BC14] §7 (freshness in EncCCA1); [CCS26] Fig. 11 (FreshR, FreshL) | Freshness side conditions are syntactic: a term avoids a set of names when none of its heads (PolyFun's `Term.heads`) is one of them (`FTerm.AvoidsNames`, `Vec.AvoidsNames`). The condition is a fold over the term and decidable for names with decidable equality, so `decide` checks it on concrete instances (`EncInstance.Syntactic`, `PRFInstance.Syntactic`, and the premises of FreshR and FreshL). It implies the semantic condition that the term's value ignores the honest-tape coordinates of those names (`FTerm.denote_update_eq_of_avoidsNames`, from `Term.denote_update_eq`), and for a closed term that its random variable does not read them (`FTerm.AvoidsNames.freshAt`). FreshR and FreshL are stated for closed terms, as a free variable ranges over all random variables, which may read the name; CCS26's "`n` fresh in `u`" is the syntactic condition. FreshR also has a form whose premise is the semantic condition in every admitted model of the hypotheses (`Valid.nonDed_freshR_of_freshAt`), as CCS26's premise `[ψ^n_fresh(u)]` is a judgment under `Θ`; the check of Pc-Oracle uses it for an oracle that uses a name without reading it. Not using a name is stronger than not reading the coordinate of one occurrence: a term that uses the key name at another index fails the check. Countermodels show that the encryption rule's syntactic conditions and FreshL's freshness are needed, and `decide` rejects the instances that break them. | closed (this fragment) | `FTerm.AvoidsNames`, `FTerm.denote_update_eq_of_avoidsNames`, `FTerm.AvoidsNames.freshAt`, `EncInstance.Syntactic`, `WorkedEnc.workedInstance_syntactic`, `EncExamples.not_keyIsCoin_syntactic`, `EncExamples.not_coinReused_syntactic`, `SecrecyExamples.not_avoidsNames_n_n`, `FreshLExamples.not_avoidsNames_n`, `Valid.nonDed_freshR_of_freshAt`, `OracleExamples.valid_puncture_nonDed`, `PRFInstance.Syntactic`, `PRFExamples.inst_syntactic` |
| L23 | choice | [LICS23] §II-B (p. 5), p. 17; [CCS26] App. C.2, footnote 2 (p. 17) | LICS23 takes the tapes to be finite bitstrings and, comparing with the base logic's infinite tapes, builds models "with long enough finite tapes (for each η)"; CCS26 extends the attacker tape "as needed". Formal counterpart: `Model.LongTapes M`, the length of the attacker tape eventually exceeds every polynomial. It is not imposed on models; FreshL, PRF-Simple, Rw-Oracle and Pc-Oracle take it as a hypothesis on the model restriction (with `Model.PolyCoins`), and a derivation using them takes it in its restriction `R₀`. It is satisfiable (tapes of at least `2^η` bits) and needed: in a model with an empty attacker tape FreshL fails. | closed | `Model.LongTapes`, `Model.longTapes_of_two_pow_le`, `FreshLExamples.longModel_longTapes`, `FreshLCountermodel.freshL_needs_longTapes` |
| L24 | choice | [CCS26] Fig. 11 caption (p. 17); [LICS23] p. 17 | The terms of FreshL (and of PRF-Simple, through it), Rw-Oracle, Pc-Oracle, PRF.R and PRF.L-sec must read the attacker tape only below a polynomial, so that the fresh name or the guessed position can be drawn above it. The bound is semantic (`FTerm.ReadsPoly`, in every admitted model of `Θ`) and discharged one constructor at a time: honest symbols and constants read nothing, a name reads what its index reads, application, conditionals, equality and negation sum the bounds of their parts, and a term computed by an admitted machine has the machine's bound (`AdvClass.readBound_mem`). Free variables range over all random variables and attacker symbols are arbitrary functions of the attacker tape (`Model.att`); their bounds are derived from `adv` hypotheses, as CCS26's caption asks every declared variable to be a name or adversarial and LICS23 adds `adv(g)` for each attacker symbol `g`, rather than imposed on models. λ and the local quantifiers are not covered: a bound uniform in the bound variable is not built. | open | `FTerm.ReadsPoly`, `FTerm.ReadsPoly.app`, `FTerm.ReadsPoly.name`, `FTerm.readsPoly_of_adv`, `Valid.readsPoly_of_adv`, `AdvClass.Adv.readsBelow`, `FreshLExamples.worked_readsPoly` |
| L25 | choice | [LICS23] Fig. 10, Prop. 17 (p. 27), p. 28; [CCS26] App. C.3 (p. 18) | `⊢pptm` is the condition that a machine computes a term; LICS23 sketches its soundness, and CCS26's PRF machines "recursively evaluate the terms". Here the machine is PolyFun's call-by-value reading `Term.denoteCBV` at one `CBVInterpretation` (`PRFSymbols.cbvInterp`): terms with calls read as free programs over the honest coins, the attacker tape and the hash oracle, with arrows read as Kleisli arrows. Its adequacy is PolyFun's fundamental lemma of logical relations, `Term.denoteCBV_related`, at the relation `PRFSymbols.CRel`: running the compiled term with the answers of the tapes and a key gives the ordinary reading. The fragment (`PRFSymbols.Pptm`, a condition on heads, decidable) mirrors LICS23's rules: variables, application and abstraction (PT.Input, PT.App, PT.Lambda), names at Boolean or base indices (PT.Name), honest and attacker symbols (PT.Adv; here of order at most one, so their values pass to and from Kleisli arrows), conditionals, Boolean constants, equality at Boolean and base types only, and calls on Boolean or base types. Local quantifiers are excluded: PT.Quant enumerates a polynomial type, which the reading does not do, and on a quantifier the reading and the term disagree. Attacker symbols read the whole tape rather than needing `adv(x)`. Polynomial time is not part of the reading: the reductions are VCVio adversaries, and efficiency enters through the class (L14). The hash oracle `λx. call x` is in the fragment (`PRFSymbols.pptm_callOracle`), and at an arrow of order one the relation gives that Kleisli application of the compiled arrow returns the arrow's reading (`PRFSymbols.evalWithAnswerFn_kapp`): that is how PRF.R's and PRF.L-sec's reductions answer the attacker's oracle input (L30). | open | `PRFSymbols.Pptm`, `PRFSymbols.PptmAt`, `PRFSymbols.cbvInterp`, `PRFSymbols.CRel`, `PRFSymbols.denoteCBV_adequate`, `PRFSymbols.lower_evalWithAnswerFn_denoteCBV`, `PRFSymbols.evalWithAnswerFn_kapp`, `PRFExamples.lower_call_r`, `PRFExamples.adequacy_needs_pptm` |
| L26 | choice | [LICS23] Fig. 1 (p. 4), p. 29; [CCS26] Fig. 11 | `ψ_msg` is generated for first-order terms (`PRFSymbols.FirstOrder`: no abstraction, so no local quantifier), whose call arguments live in the term's own context, and the conditions of enclosing conditionals are dropped, which makes the formula stronger and keeps the rule sound. LICS23's generalised subterms carry the variables bound above an occurrence and the conditions above it; neither is generated here. The semantic condition (`PRFSymbols.guardInterp`) covers abstractions, quantifying over the bound variable, and `PRFSymbols.denoteCBV_guard` holds for the whole `⊢pptm` fragment; only the syntactic formula is first order (`PRFSymbols.snd_denote_guardInterp_iff`). The vector's entries and the message are of Boolean or base type, so the distinguisher receives values. PRF.R's `ψ^{m,k}_msg(u⃗)` (`PRFSymbols.psiMsgVec`) ranges over the calls of the vector only: as in CCS26 Fig. 4, `m` may be hashed to compute `m`, and the oracle is excluded, being handled by the rule (L30). PRF.L-sec's `ψ^{m,k}_msg(u⃗, v, m)` is `PRFSymbols.psiMsg` at the vector `u⃗, v` and the message, as in CCS26 §2.3 (L32). The oracle's abstraction is the only binder on the left; it needs no generalised subterms, since no condition is generated from it, and the vector, secret and message stay first order. | open | `PRFSymbols.FirstOrder`, `PRFSymbols.calls`, `PRFSymbols.psiMsg`, `PRFSymbols.psiMsgVec`, `PRFSymbols.psiMsgVec_eq_true_iff`, `PRFSymbols.guardInterp`, `PRFSymbols.snd_denote_guardInterp_iff` |
| L27 | choice | [CCS26] App. C.1 (pp. 15–16) | `B` "samples `j` uniformly between `1` and `q(η)`, independently of the randomness used by `A` (i.e. using a part of `ρa` further away)". Bits give no exact uniform draw below `q`: `j` is spelled by `⌈log₂ q(η)⌉` bits of the attacker tape (`bitsEquiv`), uniform below `2^⌈log₂ q(η)⌉ ≤ 2q(η) + 1` (ToMathlib's `Nat.pow_clog_le_mul_add_one`), which replaces `q(η)` in the bound: at every large `η`, `deduceAdv g (u⃗, o₁) v ≤ deduceAdv g (u⃗, o₂) v + 2^⌈log₂ q(η)⌉ · Pr[o₁(m) ≠ o₂(m)]`, for `m` the named reduction's output. The bits lie above the read bounds of the attacker machine and of the terms, since the attacker tape is shared: the terms read it below a polynomial (`FTerm.ReadsPoly`) and the tapes are long, FreshL's conditions (L23, L24). `q` is the class's polynomial bound on input queries (`Machine.QueryBound`, VCVio's `IsQueryBoundP` at the input queries), a field whose polynomial-time counterpart is that time bounds query count. The averaging is one involution that swaps the drawn bits with that block of the tape. No `j` is chosen per `η`. PRF.R and PRF.L-sec bound the attacker's queries at the message by the same guess, for an event on the queried point (`prEvent_exists_firstArgs_le`). | closed (this fragment) | `Machine.guess`, `prEvent_exists_firstArgs_le`, `bitsEquiv`, `sum_prEvent_eq_two_pow_mul`, `prEvent_faultyAt_le`, `deduceAdv_le_add_faulty`, `AdvClass.queryBound_mem`, `Machine.QueryBound`, `Machine.not_queryBound_input_zero` |
| L28 | choice | [CCS26] App. C.1 (p. 15) | `A_j` returns "a default value empty if there is no such call". Carriers here are arbitrary nonempty sets of bitstrings and need not contain the empty one, and no field supplies an `η`-indexed constant, so the guess draws its default with the model's sampler for the oracles' argument type (`Machine.sampler`), which the class admits for types with polynomial bit blocks. Rw-Oracle and Pc-Oracle therefore take `Model.PolyCoins a` for the argument type `a` as a model condition, and PRF.R and PRF.L-sec, whose bounds on the attacker's queries at the message use the same guess, take it for the message type (PRF.L-sec also for the hash type, whose fresh draw it reads from the attacker tape). Taking the default from an honest constant symbol is admitted too (`AdvClass.input_mem`, with `fn_mem`), but it needs a constant of the argument type in the declaration; the sampler is used, so the rules apply to every declaration. | open | `AdvMachine.rwGuess`, `AdvClass.rwGuess_mem` |
| L29 | choice | [CCS26] Fig. 3 (p. 7), App. C.1 | Rw-Oracle is proved as App. C.1's double rule, with the deduction in the agreement premise from `u⃗, o_β` for `β = 1, 2`; Fig. 3's rule is the case `β = 1`. The oracles have type `a → b` with `a` Boolean or base, and `v` is Boolean or base: a deduction of a function compares the attacker's result with `v` at every argument, and the guess cannot know which argument's run is faulty (as for Rw-Equiv, L21). Pc-Oracle is derived from `β = 2` as CCS26 derives it, semantically; in `Derivation` it is a constructor, since that derivation concludes the agreement premise by Ineq under the hypothesis `u⃗, o′ ▷ m`, which the fragment has no rule to introduce. `o′` is the paper's λ-term (`FTerm.puncture`). The hypotheses are jointly satisfiable with `AdvClass.all`, with a conclusion that FreshR does not give, and the agreement premise is needed: an oracle that hides the secret behind the attacker's own message meets every other hypothesis, and the conclusion fails. | closed (this fragment) | `Valid.nonDed_rwOracle_of`, `Valid.nonDed_rwOracle`, `Valid.nonDed_pcOracle`, `AdvClass.NonDed.pcOracle`, `FTerm.denote_puncture`, `Derivation.nonDedRwOracle`, `Derivation.nonDedPcOracle`, `Derivation.sound`, `OracleExamples.valid_rwOracleWorked`, `OracleExamples.valid_rwOracleFig3`, `OracleExamples.rwOracle_needs_agree`, `OracleExamples.valid_pcOracleWorked` |
| L30 | choice | [CCS26] Fig. 4 (p. 7), App. C.3.1 (p. 18: "no syntactic conditions are checked on the oracle `o_h^k`, it is handled in an ad hoc way by the rule") | The hash oracle on the left is the term `λx. h(x, k)` (`PRFSymbols.hashOracle`), the closing of the term with calls `λx. call x` (`PRFSymbols.callOracle`). A reduction answers the attacker machine's input for the oracle by Kleisli-applying the compiled reading of `λx. call x` (`PRFSymbols.arrowIn`, `PRFSymbols.kapp`), one hash query per oracle query (`PRFSymbols.kapp_callOracle`), forwarded to the PRF game's oracle. The fusion lemma, an instance of `Machine.evalWithAnswerFn_simulate`, says that in the real world the run is the machine's run on the true function `h(·, k)`; the attacker's hashes are its oracle queries, from VCVio's `mem_runLog_simulateQ`. No side condition is generated from the oracle (no `ψ_msg`, no `⊢pptm` premise beyond the fixed term's), as in CCS26. | closed (this fragment) | `PRFSymbols.hashOracle`, `PRFSymbols.arrowIn`, `PRFSymbols.kapp`, `PRFSymbols.evalWithAnswerFn_simulate_arrowIn`, `PRFSymbols.simulateQ_prfRealQueryImpl_simulate_callOracle`, `PRFSymbols.exists_firstArgs_of_hashed` |
| L31 | choice | [CCS26] App. C.3.2 (pp. 22–25), Fig. 4 (p. 7) | PRF.R's proof deviates from App. C.3.2 in two places. **`m` hashed by its own run**: App. C.3.2 isolates `A₂`'s oracle call on `m̃` by guessing its index (hops 3–6), at a factor `q(η)`, and drops `A₂`'s continuation. Here `m` is a first-order term of the `⊢pptm` fragment, whose run hashes only values of its call arguments (`PRFSymbols.exists_mem_calls_of_hashed`), so among `m` and the arguments of its calls some candidate has `m`'s value and is not hashed by its own run (`PRFSymbols.exists_unhashed`, a descent on the number of calls, `PRFSymbols.calls_infix`). There is one reduction per candidate and no guess; the factor `q(η)` becomes the number of candidates, added rather than multiplied. **Order**: CCS26's `B` computes the message before running the attacker; each reduction here runs the vector, then the attacker, then the candidate, and queries the oracle at the candidate last, so that in the ideal world the challenge is a fresh draw (`PRFSymbols.eq_none_of_mem_support_run`) and the ideal hop is one bound by `2^{-cη}`, with no lazy-sampling argument. The attacker's queries at `m` (hop 2) are bounded, as in CCS26, by guessing one of them against the premise (`prEvent_exists_firstArgs_le`, L27). The premise is needed: at a constant message the attacker queries its oracle there. | closed (this fragment) | `PRFSymbols.exists_unhashed`, `PRFSymbols.calls_infix`, `PRFSymbols.rightProg`, `PRFSymbols.prEvent_prfIdealExperiment_rightReduction_le`, `prEvent_exists_firstArgs_le`, `PRFSymbols.rightAdvantage_le`, `PRFOracleExamples.prfR_needs_premise` |
| L32 | choice | [CCS26] §2.3 (p. 6), Fig. 4 (p. 7), Remark 1 (p. 21), App. C.3.1 (pp. 18–21) | **Form.** PRF.L-sec is proved as the rule of §2.3, with `ψ_msg` over `u⃗`, `v` and `m`. Fig. 4's PRF.L-X asks `ψ_msg` of `u⃗, v` only, and App. C.3.1 handles `m` hashed by its own run by guessing which of `A₂`'s oracle calls is on `m̃` and dropping `A₂`'s continuation (hops 3–4, factor `q(η)`). PRF.R's candidate argument (L31) does not carry over: the bound on "the attacker, given `h(m, k)`, queries `m`" by `C_sec` needs the challenge to be the hash of a point that the message's run has not hashed, and the candidate `t` with `m`'s value is not `m` itself. **Proof.** The reductions intercept the attacker's oracle at the message, answering it by the challenge (`PRFSymbols.interceptIn`), so the ideal worlds agree as distributions (VCVio's `OracleSpec.fst_map_run_simulateQ_romImpl_eq_of_allQueriesSatisfy`) rather than through App. C.3.1's hops; the fresh draw is then read from a block of the attacker tape (`prEvent_coin_eq_coinAt`, as in FreshL), so the last two reductions are machines on `u⃗, o_h^k`: FreshL's reduction of the attacker against the premise, and the guess of its oracle queries, with the same sampling, against `C_sec`; the conclusion's last two entries are swapped (`AdvClass.NonDed.swapLast`). **Variants.** PRF.L-eq is not done: `C_eq = u⃗, o_h^k ▷ λx. x = m` is expressible (`Ty.SecrecyOrder` allows a right side of order one), but using it needs the attacker's equality oracle to be answered by a deduced function, which no reduction here does. PRF.L-⊤ is not done: it needs a machine that answers a guessed oracle query by an input, which no closure field gives. **Checks.** Dropping `C_sec` gives PRF.L-⊤, which App. C.3.1 proves sound at a polynomial loss, so no countermodel to `C_sec` exists; the countermodels are to `ψ_msg` and to the premise. A countermodel to PRF.R without `ψ_msg` (`u⃗ = h(m, k)`) needs `h(m, k), o_h^k ⊬ m`, the one-wayness of the oracle, and is not built. | open (sec done) | `Valid.nonDed_prfLSec`, `PRFSymbols.interceptIn`, `PRFSymbols.prEvent_prfIdealExperiment_leftReduction`, `prEvent_coin_eq_coinAt`, `AdvClass.NonDed.swapLast`, `PRFOracleExamples.prfLSec_needs_psiMsg`, `PRFOracleExamples.prfLSec_needs_premise` |
| L33 | assumed | [CCS26] §2.3 (p. 5), App. B | The NoCollision lemmas (`ck(A(i)) ≠ s`, and `A(i) < A(j) ⇒ safe(A(j)) ⇒ ck(A(i)) ≠ ck(A(j))`) are proved in CCS26 App. B from collision resistance and pre-image resistance of the hash, with information-theoretic arguments; neither rule is formalized here. The ratchet's derivation takes the instances it uses as hypotheses in `Θ` (`Chain.hyps`), as CCS26's proof takes the lemmas: `[ck(h′) ≠ ck(h)]` for each position `h′` just before an update of the history `h` that `Corrupt` follows. They give PRF.L-sec's `ψ_msg` at the updates' messages, with `fst(⟨x, y⟩) = x`; at the hash queries' inputs `ψ_msg` follows by Ineq from `C_sec` and the simulation, as CCS26 argues (p. 6). They hold jointly with every other hypothesis in a perfect-PRF model, where the keys are iterates of a uniform function table from `s`, which repeat among the first `n` with probability at most `n²/2^η` (VCVio's `OracleComp.prEvent_iterate_collision_le`). | open (collision and pre-image resistance) | `Chain.noCollision`, `Chain.hyps`, `Chain.psiL`, `ChainModel.valid_noCollision`, `ChainModel.prEvent_key_iterate_collision_le` |
| L34 | choice | [CCS26] Fig. 2 (p. 4), §2.1 | CCS26's `input(τ) = att(frame(pred τ))` applies one attacker symbol to the frame, a message. Without product types the frame is a nested pair `⟨frame(pred τ), output(τ)⟩_f` of its own base type `frm` (`empty_f`, `pair_f : frm → msg → frm`), and `att : frm → msg` is the one attacker symbol, rather than one curried symbol per position. Messages have one pairing `⟨·,·⟩ : msg → msg → msg` and the first projection `fst`; `fst(⟨x, y⟩) = x` is a model condition (`Chain.FstPair`, in `Chain.ChainR`), used by WeakR (`[⟨ck, input⟩] ▷ ck`) and to derive `ψ_msg` from NoCollision. No second projection is declared: with both equations pairing is injective, which no finite carrier admits, and in every finite model of the first alone `⟨x, y⟩` depends on `x` only. A perfect PRF (a whole uniform function table as key) needs a finite message type, so a frame that keeps its outputs, as the check that safety is needed requires, has an infinite type of its own; frames are never hashed. | closed (choice) | `Chain.decl`, `Chain.frame`, `Chain.FstPair`, `Chain.dedFst`, `ChainModel.cmodel` |
| L35 | choice | [CCS26] §2.2–2.3 (pp. 4–6), Fig. 2 | CCS26 proves PFS for all traces at once, by induction over timestamps (`happens`, `<`, `pred`). Here a trace is a Lean value (`Chain.Trace`: updates and hash queries, latest first, optionally followed by one `Corrupt`), and the derivation is built by Lean recursion on its history (`Chain.chainPFS`), one derivation per trace. Timestamps, `happens` and the induction over traces in the logic are open. The safe positions are the suffixes of the history; the frame is observed at the last position (`chainPFS`) or at any position before `Corrupt` (`pfsFrame`). The schedule is fixed in advance: the attacker's inputs depend on the frame through `att`, but the order of updates, hash queries and the corruption does not. | open | `Chain.Trace`, `Chain.chainPFS`, `Chain.chainPFS_sound`, `Chain.pfsFrame_sound`, `ChainModel.valid_chainPFS`, `ChainModel.valid_pfsFrame` |
| L36 | choice | [CCS26] Fig. 2 (p. 4) | Fig. 2 sets `ck(ROM(i)) = empty`. With that definition `secrecy_base` fails at an update `A(i)` after a hash query: `ck(A(i)) = h(⟨empty, input(A(i))⟩, k)`, and from the oracle the attacker computes the frame, hence `input(A(i))`, and queries `⟨empty, input(A(i))⟩`; at `τ = ROM(i)` the PFS statement would claim `frame ⊬ empty`. Here a hash query leaves the key unchanged (`ck(ROM :: h) = ck(h)`), and every position before `Corrupt` is safe. The authors' model of the example in the tool agrees: in [SQUIRREL-REPO]'s `examples/secrecy-ccs-2026/motivating-example.sp`, `ck` is a mutable cell that only `A` and `Corrupt` assign, and the process `ROM` does not touch it. A countermodel to Fig. 2's literal definition is not built. | closed (choice) | `Chain.ck` |
