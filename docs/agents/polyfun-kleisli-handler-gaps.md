# PolyFun Kleisli / monadic-handler theory gaps (stress-test findings)

This is the **pays-rent ledger** for the "Katz–Lindell as a thin layer over PolyFun" program:
concrete places where proving Stage-5 crypto (PRF, CPA) on the polynomial-functor base layer was
harder than it should be because the base layer is missing generic *Kleisli-category /
monadic-handler* theory. Each entry names the lemma(s) I had to hand-prove or the workaround I
had to install, so the corresponding upstream PolyFun theorem is falsifiable: **land it upstream
and the VCVio-side boilerplate/workaround deletes.**

These are structural (monad-parametric) facts, so they belong in PolyFun's crypto-free layer, not
in VCVio. Route the fixes through the next stacked PolyFun PR and update
`PolyFun/docs/reading/roadmap.md` (do not edit the pinned package in place).

Evidence files: `VCVio/OracleComp/Coinductive/WireK.lean`,
`VCVio/CryptoFoundations/Asymptotics/Game/Challenger.lean`,
`VCVio/CryptoFoundations/PRFGame.lean`, `KatzLindell/Chapter03/CPA.lean`,
`VCVio/OracleComp/SimSemantics/StateT/Basic.lean`, `VCVio/OracleComp/SimSemantics/SimulateQ.lean`.

---

## G1. Naturality of the universal fold along a monad morphism is not assembled

**What's missing.** `simulateQ` is the universal fold out of the free monad `FreeM p`, and it is
*already* packaged as a monad morphism: `simulateQ' impl : OracleComp spec →ᵐ r`
(`SimSemantics/SimulateQ.lean:43`), with `MonadHom` (`→ᵐ`), `∘ₘ`, and `MonadHom.ofLift` all
present in `VCVio/EvalDist/`. What is **not** stated is the naturality square

```
φ ∘ₘ simulateQ' impl  =  simulateQ' (φ ∘ impl)      for any monad morphism φ : r →ᵐ r'
```

together with its `StateT`-transported form (`StateT σ` is a functor on `→ᵐ`). Both are immediate
from the universal property (both sides are monad morphisms out of the free monad agreeing on
generators), so this is a one-shot `FreeM`-level theorem.

**Rent it's paying now (all hand-proved by `OracleComp.inductionOn`, one shape each):**

- `ProbResponder.run_simulateQ_toQueryImpl_ofStateQueryImpl` (`WireK.lean`) — I added this: it is
  exactly naturality of `𝒟 : ProbComp →ᵐ SPMF` transported through `StateT σ`
  (`𝒟 ∘ simulateQ impl = simulateQ (𝒟 ∘ impl)`), proved by a bespoke induction. It is the single
  reusable bridge every stateful-responder consumer needs (used by `PRFGame` and `CPA`).
- `OracleComp.simulateQ_stateless_run` (`Challenger.lean`) — same shape for the trivial-state
  embedding.
- `evalDist_simulateQ_run'_eq_evalDist`, `evalDist_simulateQ_run_congr`
  (`SimSemantics/StateT/Basic.lean`) — pre-existing, same shape, distribution-preserving handlers.

**Upstream theorem (P7/B6-adjacent).** `FreeM.mapM` naturality along a monad morphism, plus a
`MonadHom`-functoriality lemma for `StateT`. Then the four lemmas above collapse to one-liners, and
the SPMF↔ProbComp / state-marginalization bridges stop being re-derived per call site. This is the
"handlers are Kleisli maps, monad morphisms are the 2-cells, the fold is functorial" content.

---

## G2. Coalgebra carriers (`.State`) are opaque to `simp`/`rw`, and the opacity is contagious

**What's wrong.** `ProbResponder.State`, `Challenger.State := (responder n).State`, and
`(PFunctor.DynSystem …).State` do **not** reduce at the transparency `simp`/`rw` use
(reducible/instances) even when they are `rfl`-equal to a concrete carrier. This is the same wall
recorded for `(M.wrapIface w).State = M.State` in the reductions milestone. It is not cosmetic — it
is **contagious**:

- `(ProbResponder.ofStateQueryImpl impl).State` won't reduce to `σ`, so instance synthesis fails
  (`EmptyCollection (prfIdealResponder n).State` in `PRFGame`, worked around by annotating the empty
  cache with its concrete type), and `StateT.run_map` / `bind_map_left` / `evalDist_bind` will not
  match a `.run`/bind whose intermediate type is the carrier.
- **The killer:** `Challenger.setup : (n) → SPMF ((responder n).State × α n)` bakes `.State` into the
  sampled state, and that `.State` then infects the *intermediate type of every downstream `bind`*.
  A `change`/type-ascription at the leaves does **not** override a `bind`'s type parameter — Lean
  keeps `.State` to stay defeq to the goal. This defeated a clean
  `advantage_toProgGame_ofStateOracle` (the stateful analogue of the working
  `advantage_toProgGame_ofProbHandler`): the responder run rewrite produced a type-broken `bind`
  every time.

**Why the memoryless case works and the stateful case doesn't.** `advantage_toProgGame_ofProbHandler`
succeeds because its former routes through `QueryImpl.stateless (α n) H`, which takes the carrier
`α n` as an **explicit argument** — so `StateT (α n)` is syntactic, never `.State`. The moment the
carrier is hidden behind a structure projection, every rewrite through it breaks.

**Consequence for this milestone.** I could not identify the *stateful* `Challenger.toProgGame`
advantage with a concrete `ProbComp` experiment. CPA's security notion (`CPASecure`) is therefore
built on a standalone concrete `cpaExp` plus a ProbComp-level responder bridge (`run_cpaResponder_eq`),
**not** on `cpaChallenger.toProgGame`. `cpaChallenger` still exists for the machine-game reading, but
its program-game ⇔ `cpaExp` identity is left as a documented gap.

**Fixes (either suffices; PolyFun should pick one as an API discipline):**
1. Ship `@[simp]` carrier-reduction lemmas as part of the `DynSystem`/responder API (a `State`
   normal-form discipline). I installed the local instance of this — `@[simp] ofStateQueryImpl_state`
   in `WireK.lean` — which unblocked the *targeted* run rewrites but not the `bind`-intermediate-type
   contagion. A systematic version (carriers reduce everywhere, including in `StateT`/`bind` type
   args) is what's needed.
2. Have the stateful formers expose the carrier as an explicit parameter, the way
   `QueryImpl.stateless` does. This is the robust fix: it makes the carrier syntactic and the
   `ofProbHandler`-style `change` proof technique work verbatim for stateful challengers.

---

## G3. No theory of handler morphisms / how the wired run transforms under them

**What's missing.** Every combinator on the challenger side is a morphism of handlers (a map in the
(co)Kleisli category of `PFunctor.Handler`/`ProbResponder`), and every theorem about it is "the wired
run transforms functorially under this morphism." PolyFun deliberately has **no** monadic-responder
type (`ProbResponder ≈ Handler (StateT σ m) q` is the stance), and correspondingly **no** theory of
handler morphisms and their commutation with `runWith`/`wireKRun`. So each combinator's run law is
re-derived VCVio-side from scratch:

- `wrapIface ⊣ pullback` (reductions milestone): `runK_wrapIface` proved by fuel induction.
- `ProbResponder.pullback` interface translation: `toQueryImpl_pullback` + its run interaction.
- `ProbResponder.ofStateQueryImpl` bridge (G1).
- the un-built `switchAt` (G4) and `simulate` will each need their own bespoke run law.

All of these are instances of one absent theorem: **`runWith` (equivalently `wireKRun`, the eval-wired
game) is a functor on handler morphisms.** With it, `wrapIface`, `pullback`, the `𝒟`-bridge, and the
hybrid splice below are corollaries rather than separate inductions.

**Upstream home.** This is the "Kleisli category theory" the stress-test keeps hitting — B4/B5
retrofunctor territory (P9), or a lighter "morphisms of `Handler` and `runWith`-functoriality" pack
that does not need the full §7.3.3 quadruple.

---

## G4. The hybrid ladder is responder surgery with no upstream `◁`-splice

**Status.** Not built this milestone (Stage-5 `Hybrid.lean`/`PrivKMult.lean` remain). Recording the
gap from the design so far:

The clean dynamical-systems hybrid device is `ProbResponder.switchAt (j) (R₁ R₂)` — a responder whose
state is `query-counter × R₁.State × R₂.State`, answering via `R₁` before the `j`-th query and `R₂`
after. The rung games are challengers over `switchAt j`, and the ladder telescopes. But proving the
rungs telescope needs exactly the handler-composition/decomposition theory of G3 (splicing two
handlers at a frontier), which upstream calls out as `◁`-convolution / `comultN` (Prop 7.20d, the
roadmap's N3 pays-rent test) but does **not** connect to the *probabilistic* responder. Today the only
working hybrid ladders in the repo are VCVio-side and specialized: `IND_CPA_hybridChallengeOracleLR_counted`
(a `leftUntil` threshold baked into one oracle) and `StateSeparating/Hybrid.lean`. A generic
responder-level `switchAt` + telescoping is what P8 (hybrid-ladder combinators) should deliver so these
stop being per-scheme.

---

## Summary table

| Gap | VCVio rent today | Upstream fix | Roadmap ticket |
|-----|------------------|--------------|----------------|
| G1 fold naturality along `→ᵐ` | 4× hand-proved `simulateQ`/`𝒟` inductions | `FreeM.mapM` naturality + `StateT`-on-`→ᵐ` | P7/B6 |
| G2 opaque coalgebra carriers | `.State` annotations, `@[simp] ofStateQueryImpl_state`; blocked stateful `toProgGame` characterization | carrier normal-form discipline **or** explicit-carrier formers | (new; API discipline) |
| G3 handler-morphism / `runWith` functoriality | `wrapIface`, `pullback`, `ofStateQueryImpl` run laws each hand-proved | `runWith` is a functor on handler morphisms | P9 (or lighter pack) |
| G4 hybrid `◁`-splice for responders | per-scheme threshold oracles | responder `switchAt` + telescoping | P8 |

**Headline verdict.** The polynomial-functor base layer gives clean *objects* (handlers = Kleisli
maps, the fold = a monad morphism, the game = eval-wiring), but the *2-cell* layer — morphisms of
handlers and the functoriality of the fold / wired run under them — is absent, so every probability
bridge and every reduction combinator is re-proved by induction. G1 and G3 are the same missing idea
at two altitudes (fold vs. run); G2 is the reducibility discipline that would make either usable
without fighting defeq.
