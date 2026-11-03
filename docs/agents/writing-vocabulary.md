# Writing Vocabulary

Use this page with the [writing standard](writing.md). STE's general dictionary remains the
reference for general words, meanings, and grammatical roles. This page adds subject-field terms
and advice for VCVio prose. It does not replace the dictionary or list every permitted English
word. The [notation reference](notation.md) owns the meaning of each Lean notation.

## How to add a term

1. Find the concept in the VCVio source, Mathlib, Lean documentation, or the cryptographic
   literature.
2. Prefer the established term over a local synonym.
3. Record the intended meaning and grammatical role when the word can cause ambiguity.
4. Use a qualifier when two technical meanings occur in the same passage.
5. Add a missing term or meaning when the contribution first needs it.

One spelling can be a technical noun and a technical verb, as in "a query" and "query an oracle".
STE permits this dual role when each use meets the rules for its category (STE 1.7, 1.12, 1.13).
Record the noun and the verb uses separately. A category example is not a reason to reject another
established term from the same field.

## Terms and context

These distinctions help a reader identify the intended concept. They do not prohibit the ordinary
meaning of a word in a different context:

| Term | Technical use | Clarify when necessary |
|---|---|---|
| adversary | A computation that attacks a scheme in a security experiment | Name its oracle access and any resource bound. An adversary type alone carries no resource bound. |
| advantage | The quantity that a security theorem bounds for an adversary | Name the experiment and the adversary. Say whether the bound is exact or asymptotic. |
| bound | A numerical constraint, as a noun | As a verb, state which quantity it bounds. Write "query bound" or "probability bound" when both occur. |
| check | A test or condition, as a noun | As a software verb, it means to evaluate a specified condition or test. |
| complete, completeness | The completeness property of a protocol or a scheme | Ordinary uses such as "complete the template" remain permitted. Name the property in security text. |
| distribution | The output measure of a computation, `evalDist` or `𝒟[…]` | Say "output distribution" when a distribution over inputs or keys also occurs. |
| experiment | A program that runs an adversary and returns a result, such as a Boolean | An experiment is a computation, not a measure. The [naming rules](crypto.md#naming) give its declaration names. |
| game | A hidden-bit experiment, or an intermediate game of a game-hopping proof | Do not use "game" for every experiment. A "game hop" compares two consecutive games. |
| failure | The probability mass that is absent from the output distribution, measured by `prFail` | Do not use "failure" for a rejected input, a build error, and missing mass in one passage. |
| field | An algebraic field or a member of a structure | Write "structure field" when the distinction matters. |
| handler | A query implementation, `QueryImpl`, that answers the queries of a computation | Name the oracle specification that it answers. |
| instance | A typeclass instance or a problem instance of a hardness assumption | Qualify the instance when both meanings occur. |
| kernel | A Markov kernel of Mathlib, or the Lean kernel that checks proofs | Write "Markov kernel" or "Lean kernel" when the distinction matters. |
| key | A cryptographic key or the key of a map, such as a cache entry | Write "secret key", "public key", or "cache key" when both occur. |
| lossless | A computation whose output distribution has total mass one | Under an answer measure, every `OracleComp` computation is lossless. Failure arises in transformers such as `OptionT`. |
| module | A Lean module or an algebraic module, as in module lattices | Write "Lean module" or "module over `R`" when the distinction matters. |
| proof | A Lean proof, a mathematical proof, or a proof-system object | Name the kind of proof before comparing different kinds. |
| reduction | A named computation that turns one adversary into another | Name the reduction in a security theorem. Do not state only that one exists. |
| sound, soundness | A specified soundness property of a protocol | Name the property and its assumptions. Ordinary prose can use "correct" for an argument. |
| spec | An oracle specification, `OracleSpec` | Write "specification" or the standard name, such as FIPS 205, for a document. |
| statement | A theorem's proposition or the public input of a relation | Use "theorem statement" or "protocol statement" when both meanings occur. |
| support | The set of possible outputs of a computation, `support` | Do not use "support" for library coverage in the same passage. |
| valid | Satisfaction of a specified predicate or well-formedness condition | Name the predicate. Do not replace "valid signature" with "accepted signature" unless they mean the same thing. |
| verify | A verifier's action, or a check by the Lean kernel | Use "check" for routine repository tests. Name the relevant predicate or result. |

## Technical nouns

These examples identify relevant subject fields. Preserve established terms and their spellings.
Introduce a longer or unfamiliar term before you use an abbreviation:

| Field | Examples |
|---|---|
| Oracle computations | oracle specification, oracle computation, query, query implementation, handler, simulation, query log, query bound, cache, subspecification |
| Probability | output distribution, measure, Markov kernel, event, probability, failure probability, support, equality in distribution, uniform sampling, coupling |
| Program logic | weakest precondition, Hoare triple, relational triple, postcondition, invariant |
| Security definitions | adversary, experiment, game, advantage, reduction, simulator, extractor, distinguisher, hybrid, game hop, negligible function |
| Cryptographic constructions | encryption scheme, signature scheme, commitment scheme, KEM, DEM, sigma protocol, identification scheme, random oracle, Fiat–Shamir transform, forking lemma |
| Security properties | correctness, completeness, soundness, special soundness, zero knowledge, hiding, binding, IND-CPA, EUF-CMA, SUF-CMA |
| Lattices and hashing | module lattice, learning with errors, short integer solution, ML-KEM, ML-DSA, Falcon, SLH-DSA, hash function, extendable-output function |
| Lean | declaration, theorem, lemma, hypothesis, docstring, namespace, typeclass, instance, tactic, elaboration, axiom, Lean module |
| Repository tools | branch, commit, pull request, build, linter, axiom baseline, validation, merge queue, CI |

## Technical verbs

Use these verbs for the stated subject-field actions. Keep a verb's meaning consistent within a
passage. Explain the operation or name the relevant declaration when its meaning is not clear:

| Field | Examples of actions |
|---|---|
| Oracle computations | query an oracle, answer a query, simulate a computation with a handler, log queries, cache answers, program a random oracle |
| Probability | sample a value, bound a probability, couple two computations, condition on an event |
| Security proofs | reduce one problem to another, extract a witness, rewind an adversary, fork a computation, distinguish two games |
| Cryptographic constructions | sign a message, verify a signature, encrypt a message, decrypt a ciphertext, commit to a value, open a commitment |
| Mathematics | prove a claim, define an object, assume a hypothesis, bound a quantity |
| Lean | instantiate a variable, specialize a theorem, unfold a definition, rewrite an expression, elaborate a term, expose a definition |
| Repository tools | build a target, run a linter, validate a change, rebase a branch, merge a pull request, enqueue a pull request |

## Words to avoid

This table gives prompts for an editing pass over ordinary prose. They do not define STE word
approval. Use a replacement only when it preserves the meaning and grammatical role. Rewrite the
sentence when a direct replacement does not work:

| Avoid | Use |
|---|---|
| "utilize", "leverage", "make use of" | use |
| "ensure" | make sure that, or name the condition and the action |
| "in order to" | to |
| "prior to", "subsequent to" | before, after |
| "in the event that" | if |
| "comprised of" | has, contains |
| "a number of", "various" | the number, or "some", if the quantity is not specified |
| "e.g.", "i.e.", "etc." | for example, that is, the full list |
| "cf.", "resp.", "w.r.t.", "wlog" | compare, explicit pairings, with respect to, without loss of generality |
| "respectively" | explicit pairings when the reference would otherwise be unclear |
| "robust", "seamless", "comprehensive", "powerful", "elegant", "crucial" | the measurement or the reason |
| "clearly", "obviously", "trivially", "basically" | the reason, or delete the word |
| "it is worth noting that", "it is important to" | delete the phrase when it adds no information |
| "now", "no longer", "previously", "formerly", "currently", "new" | in library reference text, the fact about the present state (rule C3) |

"The following are equivalent" is a permitted mathematical introduction. Words such as "simply"
and "essentially" can occur in technical terms, such as "simply typed" and "essentially
surjective". Review their meaning rather than deleting them as isolated words. "Negligible" and
"tight" are technical terms in security proofs. They are not vague qualifiers.
