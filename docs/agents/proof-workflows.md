# Proof Workflows

## Proof Strategy Decision Tree

**What are you trying to prove?**

1. **Two games have the same distribution** (`g₁ =ᵈ g₂`):
   → `by_equiv` to enter relational mode, then use `rvcstep` / `rvcgen`
   → Add `using ...` when the current relational step needs an explicit witness

2. **Advantage is bounded** (`advantage ≤ ε`):
   → `by_dist` to enter TV distance reasoning
   → Use `by_dist ε₂` when you want to pin the TV-distance contribution explicitly
   → For identical-until-bad: use `by_upto` or
     `measureETVDist_simulateQ_run'_le_prEvent_bad` (`Relational/SimulateQ/UntilBad.lean`)

3. **Probability equals a specific value** (`Pr{let y ← oa}[y = x] = ...` or `Pr{let x ← oa}[p x] = ...`):
   → Use `prvcgen` when the value holds on every outcome (`= 0`, `= 1`) or a loop invariant pins
    it; it splits `= c` into an upper and a lower bound, and proves bounds `r ≤ Pr{…}[…]`,
    `Pr{…}[…] ≤ ε` and core triples the same way
   → Use `simp only [expect_norm, expect_eval]` to state the expectation through the program's
    unfolding and the values of its draws; `simp` averages finite uniform draws
   → Otherwise use `prEvent_bind_eq_lintegral_of_discrete` (or `prEvent_bind_eq_lintegral`) to
    decompose binds manually into `∫⁻ x, … ∂𝒟[oa]`
   → Use `simp` with project simp lemmas
   → Use `prrw`, `prrw congr`, or `prrw normalize` when the value is another program's probability

4. **Multi-hop security proof** (`g₁ =ᵈ gₙ`):
   → `game_trans g₂` to split into two goals, repeat

5. **Need to swap sampling order**:
   → Use `prrw` (or `prrw under n` below shared binds) for one swap; it closes the goal when the
    two sides then agree
   → Use `prrw normalize` to search for a sequence of swaps and shared-prefix steps that closes it

## Monadic Normalization with `monad_norm`

The canonical way to normalize monadic expressions in this codebase is Mathlib's
`monad_norm` simp set (declared in `Mathlib.Tactic.Attr.Register`). It bundles
`pure_bind`, `bind_assoc`, `bind_pure`, `map_pure`, `pure_seq`, `seq_assoc`,
`seq_eq_bind_map`, and `map_eq_bind_pure_comp`, which between them push goals
toward an associated bind-canonical form.

Prefer `simp [monad_norm]` (or `simp […, monad_norm]`) over hand-rolled lemma
lists like `simp [bind_assoc, pure_bind, …]`. It documents intent, keeps proofs
robust if Mathlib adds further rules, and reads more clearly. In `simp only`
calls it is fine too — `simp only [monad_norm]` is just the closed set.

When it isn't feasible:

- **Direction-flipping conflicts.** `monad_norm` rewrites `f <$> x` toward
  `x >>= pure ∘ f`. Proofs that deliberately use `bind_pure_comp` /
  `map_pure` to keep the goal in `<$>` form (common in StateT-heavy proofs in
  `Examples/CommitmentScheme/Hiding/*` and large stretches of
  `VCVio/CryptoFoundations/ReplayFork.lean`) will break, because a downstream
  `rw [some_lemma_about_<$>]` no longer matches. Keep the explicit lemma list
  at those sites.
- **Tightly tuned `simp only` chains.** When a proof relies on a *specific*
  partial-rewrite state between two `simp only` calls (e.g. peeling structure
  before a `simp_rw [hpeel, …]`), folding `monad_norm` into the earlier call
  can over-rewrite. Leave the two-pass structure alone.
- **`rw` and `simp_rw` lemma lists.** These take individual lemmas, not simp
  sets — `monad_norm` doesn't apply.
- **Files that don't import `Mathlib.Tactic.Attr.Register`.** A few low-level
  files in `ToMathlib/Control/Monad/` (e.g. `Indexed.lean`, `Graded.lean`)
  import only `Mathlib.Algebra.…` and don't see `monad_norm`. Don't widen
  imports just to use it; spelling out `bind_assoc` is fine there.

Treat `monad_norm` as the default and the manual lemma list as the exception.
When you do choose the manual list, the choice is usually load-bearing — leave
a one-line comment explaining what shape downstream needs.

## Game-Hopping Recipe

### Step 1: State the security theorem

```lean
theorem myScheme_secure :
    myAdvantage adversary ≤ q * ddhAdvantage (myReduction adversary) := by
```

### Step 2: Define intermediate games (hybrids)

```lean
def hybrid (adversary : ...) (k : ℕ) : ProbComp Bool := do
  -- first k queries use real, rest use random
  ...
```

### Step 3: Telescope via `game_trans`

```lean
  game_trans (hybrid adversary 1)
  · -- prove hybrid 0 =ᵈ hybrid 1
    by_equiv
    ...
  · game_trans (hybrid adversary 2)
    · ...
```

### Step 4: Per-hop reduction

For each hop, build a reduction adversary that embeds the DDH challenge at position k:

```lean
def stepReduction (adversary : ...) (k : ℕ) : DDHAdversary F G :=
  fun x x₁ x₂ x₃ => do
    -- use (x, x₁) as public key
    -- at query k, return (x₂, msg * x₃) instead of encrypting
    ...
```

### Step 5: Prove per-hop equivalence

Show that DDH-real corresponds to hybrid k and DDH-random corresponds to hybrid k+1.

## Worked Example: OneTimePad Privacy

From `Examples/OneTimePad/Basic.lean` — the canonical complete proof.

**Setup**: OTP encrypts by XOR with a uniformly random `BitVec` key.

```lean
def oneTimePad (sp : ℕ) :
    SymmEncAlg ProbComp (BitVec sp) (BitVec sp) (BitVec sp) :=
  oneTimePadOfKeygen sp ($ᵗ BitVec sp)   -- encrypt k m := return k ^^^ m
```

**Privacy proof sketch**:
1. The ciphertext is `c = k ^^^ m` where `k` is uniform
2. XOR with a fixed `m` is a bijection, so `k ^^^ m` is uniform for every `m`
3. So every message has the same ciphertext measure, `uniformOn Set.univ`, and the rows are
   equal in distribution (`=ᵈ`)

**Key technique**: `evalDist_xor_uniformSample` (`VCVio/OracleComp/Constructions/BitVec.lean`)
computes `𝒟[(· ^^^ msg) <$> $ᵗ BitVec sp] = uniformOn Set.univ`; `EvalDistEq.of_evalDist_eq`
turns the equal measures into `=ᵈ`.

## Worked Example: ElGamal IND-CPA

From `Examples/ElGamal/Basic.lean` — multi-query security via the generic one-time DDH lift.

**Key patterns used**:
- Define ElGamal correctness and the one-time DDH bridge.
- Prove that the one-time advantage is twice the DDH advantage of the reduction.
- Instantiate `AsymmEncAlg.IND_CPA_Advantage_le_mul_of_oneTime_bound`.
- Final bound: `IND_CPA_Advantage ≤ q * (2 * ε)`, where `IND_CPA_Advantage` is the Boolean bias
  `Measure.boolBias` of the oracle IND-CPA game `AsymmEncAlg.IND_CPA_Game`.

For tactic-heavy hybrid proofs, use the generic recipe above or the focused
examples under `Examples/ProgramLogic/`.

## Annotated Tactic Usage

### `by_equiv` + relational decomposition

```lean
-- Goal: g₁ =ᵈ g₂
by_equiv                    -- now: ⟪g₁ ~ g₂ | EqRel α⟫
rvcstep using R         -- if needed, provide the bind cut relation
· rvcstep using f       -- couples the sampling step with a bijection
  · exact hf
  · intro x
    exact hR x
· intro a b hab
  subst hab
  rvcgen                    -- keep taking obvious relational steps
```

When there is exactly one viable local hypothesis that works as a `using` hint,
plain `rvcstep` and `rvcgen` will auto-consume it — no explicit `using` needed:

```lean
-- hf : ∀ a₁ a₂, S a₁ a₂ → ⟪f₁ a₁ ~ f₂ a₂ | R⟫ is the only viable hint
rvcgen                      -- auto-selects hf as the bind-cut relation
```

If there are 0 or ≥ 2 viable hints, the tactic keeps ambiguity explicit and
falls back to `EqRel`. Use `using` to disambiguate.

The opt-in relational finish pass also handles postcondition weakening:

```lean
-- Goal: ⟪oa ~ ob | R'⟫ with h : ⟪oa ~ ob | R⟫ and hpost : ∀ x y, R x y → R' x y
rvcgen!                     -- runs rvcgen, then rvcfinish
```

Use plain `rvcgen` when you only want structural steps plus cheap leaf closure;
use `rvcfinish` or `rvcgen!` when residual consequence/search is intended.

```lean
-- Same workflow, but ask the tactic to surface the explicit script:
rvcstep?
```

On bind goals, the replay can surface the full tuple naming form:

```lean
rvcstep using S as ⟨a1, a2, hrel⟩
```

### `prrw` on probability equalities

```lean
-- Goal: Pr{let x ← $ᵗ P; let b ← $ᵗ Bool; let z ← f x b}[z = true]
--     = Pr{let b ← $ᵗ Bool; let x ← $ᵗ P; let z ← f x b}[z = true]
prrw                  -- swaps the first two draws, which closes the goal
```

```lean
-- Alternatives: the swap below one shared draw, or a search for a closing sequence of steps
prrw under 1
prrw normalize
```

```lean
-- Expose a shared prefix, naming the value and its support hypothesis:
prrw congr as ⟨x, hx⟩
```

### `prvcgen` on bounds and triples

```lean
-- Goal: r ≤ Pr{let x ← oa}[p x], with h : ⦃ r ⦄ oa ⦃ fun x => 𝟙⟦p x⟧ ⦄ in context
prvcgen                     -- lower-bound reading; `vcgen` uses `h`
```

A continuation specified only on the support of the first program uses `Spec.ofSupport`, which
leaves the support membership:

```lean
-- Goal: ⦃ 1 ⦄ (do let x ← oa; f x) ⦃ fun y => if y = true then 1 else 0 ⦄
-- with h' : ∀ x ∈ support oa, ⦃ 1 ⦄ f x ⦃ fun y => if y = true then 1 else 0 ⦄
prvcgen [OracleComp.Lower.Spec.ofSupport oa, h']
exact Subtype.property _
```

A loop takes an invariant, as an explicit rule or through `invariants`:

```lean
-- Goal: ⦃ pre ⦄ oa.replicate n ⦃ post ⦄, with hstep : ⦃ I ⦄ oa ⦃ fun _ => I ⦄
prvcgen [triple_replicate_inv hstep]
all_goals simp_all          -- pre ≤ I and I ≤ post xs

-- Goal: ⦃ I s₀ ⦄ l.foldlM f s₀ ⦃ I ⦄, with hstep : ∀ s x, x ∈ l → ⦃ I s ⦄ f s x ⦃ I ⦄
prvcgen invariants · fun _ _ s => I s
all_goals simp_all
```

A sub-program without a rule is left as its weakest precondition:

```lean
prvcgen (errorOnMissingSpec := false)
simp only [expect_norm, le_refl]
```

### Rules for opaque programs

An `@[irreducible]` program is opaque to `vcgen`. State its triple as a core `@[spec]` rule
(`@[local spec]` for one file):

```lean
@[irreducible] def wrappedTrue : OracleComp spec Bool := pure true

@[local spec] theorem triple_wrappedTrue :
    ⦃ 1 ⦄ wrappedTrue (spec := spec) ⦃ fun y => if y = true then 1 else 0 ⦄ := by
  simpa [wrappedTrue] using
    (Std.WP.Spec.pure (m := OracleComp spec) (post := fun y => if y = true then 1 else 0) true)
```

`prvcgen` then uses the rule wherever `wrappedTrue` occurs; without the attribute,
`prvcgen [triple_wrappedTrue]` passes it for one call. Relational rules register with `@[vcspec]`
instead.

If an exhaustive `rvcgen` run stops too early, raise the local pass budget with:

```lean
set_option vcvio.vcgen.maxPasses 128 in
  rvcgen
```

For tactic-choice debugging, enable the planned-step trace locally:

```lean
set_option vcvio.vcgen.traceSteps true in
  rvcstep
```

### `by_dist` for advantage bounds

```lean
-- Goal: AdvBound game ε
by_dist                     -- enters TV distance mode
-- now need to show measureETVDist ... ≤ ε
```

```lean
-- Same shape, but fix the TV-distance contribution first:
by_dist ε₂
```

## Reusing `preInsert` / `postInsert` Theory

When a goal mentions `simulateQ` of a `QueryImpl` wrapper from `QueryTracking/`
(`countingOracle`, `loggingOracle`, `withCost`, `withLogging`, `withTraceBefore`, etc.) or
any custom wrapper built on `preInsert` / `postInsert`, **prefer the generic bridge lemmas
from `VCVio/OracleComp/SimSemantics/QueryImpl/Constructions/Core.lean` over re-proving the
specific instance.** The bridges are parameterised over a projection
`proj : ∀ {γ}, n γ → m γ` (typically `Prod.fst <$> WriterT.run ·` for a writer-style
wrapper, or `(·.run s) >>= ...` for a state-style wrapper). The projection equation is an
equality of computations, so output measures `𝒟[…]` and events `Pr{…}[…]` transfer by
rewriting with it:

| Lemma family | What it gives you |
|---|---|
| `proj_simulateQ_preInsert` / `proj_simulateQ_postInsert` | Strip the instrumentation: `proj (simulateQ (so.preInsert nx) oa) = simulateQ so oa`. |
| `support_proj_simulateQ_*` / `finSupport_proj_simulateQ_*` | Output-marginal support / `Finset` support is unchanged. |
| `simulateQ_preInsert.induct` / `simulateQ_postInsert.induct` (`@[elab_as_elim]`) | Induction principle parametric in the projection — useful when the bridges above are too rigid. |

For query-bound transfer through a wrapper, see
`isTotalQueryBound_simulateQ_preInsert` / `…_postInsert` (and the predicated
`IsQueryBoundP` versions) in `QueryTracking/QueryBound.lean`.

If you find yourself writing an inductive proof that "running my wrapper preserves the
output measure" and the wrapper is built on `preInsert` / `postInsert`, the proof is almost
certainly a one-line rewrite with `proj_simulateQ_preInsert` (or its `postInsert` sibling)
under the right projection. Reach for the bridge before reaching
for `OracleComp.inductionOn`.

## Asymptotic Security Reductions

For proofs involving asymptotic security (negligible advantage), use the lemmas in
`VCVio/CryptoFoundations/Asymptotics/Security.lean`.

### Tight reduction

```lean
exact secureAgainst_of_reduction hreduce hbound hsecure
```

where `hbound : ∀ A n, g.advantage A n ≤ g'.advantage (reduce A) n`.

### Polynomial-loss reduction

```lean
exact secureAgainst_of_poly_reduction hreduce hbound hsecure
```

where `hbound : ∀ A n, g.advantage A n ≤ ↑(loss.eval n) * g'.advantage (reduce A) n`.
Uses `negligible_polynomial_mul` under the hood.

### Game hop (absorb negligible difference)

```lean
exact secureAgainst_of_close hε hclose hsecure
```

where `hclose : ∀ A, isPPT A → ∀ n, g₁.advantage A n ≤ g₂.advantage A n + ε n`.

### Hybrid argument

```lean
exact secureAgainst_of_hybrid hε hconsec hsecure
```

Takes a chain of `k+1` games where consecutive games differ by at most `ε(n)`.
Proves by induction, applying `secureAgainst_of_close` at each step.

## Parallel Agent Workflow

When parallelizing proof work across multiple agents, use one `git worktree` per task so
each agent gets an isolated checkout:

```bash
git worktree add ../vcv-task-a HEAD
git worktree add ../vcv-task-b HEAD
```

Guidelines:

- Keep same-file follow-up tasks sequential rather than parallel.
- Merge the first wave before dispatching dependent follow-up tasks.
- Prefer one prompt or one proof chunk per worktree to reduce conflicts.
- Keep committed prompt files available to all worktrees if downstream agents need them.

This pattern is especially useful for sorry-filling and multi-file proof searches.

## Reference-First Workflow

For relational logic work, consult
*A Quantitative Probabilistic Relational Hoare Logic* ([ERHL25](../../REFERENCES.md#erhl25))
before changing definitions or tactics for eRHL, pRHL, or apRHL.

## Debugging Common Stuck States

### "typeclass instance problem ... HasQuery spec ?m" or "Monad (OracleQuery spec)"
After the `HasQuery` cutover, the bare `query t` is `HasQuery.query t` and needs an expected type so Lean can pick the ambient monad. Either ascribe `(query t : OracleComp spec _)`, or use the primitive form `spec.query t : OracleQuery spec _` (e.g. when applying `liftM` or projecting `OracleQuery.cont`).

### "failed to synthesize ... OracleSpec.AnswerMeasure spec"
For `OracleComp spec`, add answer measures with `[OracleSpec.AnswerMeasure spec]` when you need `𝒟[...]` or `Pr{...}[...]`, and `[OracleSpec.UniformAnswerMeasure spec]` for uniform answers and cardinality facts. If the answer types are finite and nonempty and you intend uniform semantics, install a local instance with `UniformAnswerMeasure.ofFiniteNonempty spec`. `𝒟[...]` also needs a `MeasurableSpace` on the result type.

### Universe mismatch around `SubSpec`
`OracleComp` has 3 universe parameters, `SubSpec` has 3. Use `{ι : Type*}` instead of `{ι : Type u}` to let universes resolve independently.

### `simp` does not integrate an event over a bind
`prEvent_bind_eq_lintegral` is not a `simp` lemma. Use `rw [prEvent_bind_eq_lintegral_of_discrete]` when the common draw has a discrete measurable space, or `prEvent_bind_eq_lintegral` with a measurability proof for the continuation.

### Aggressive unfolding of `OracleComp`
Core types are `@[reducible]`. Lean may unfold `OracleComp` to `PFunctor.FreeM`. Use `OracleComp.inductionOn` as the canonical eliminator, not pattern matching on `PFunctor.FreeM.pure`/`roll`.
