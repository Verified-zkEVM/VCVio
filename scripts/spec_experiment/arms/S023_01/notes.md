# S023_01 replayPathResult_mem_support_replayFirstRun — arm A

- Minutes: ~3
- Result: 5 lines / 574 HB (original 7 / 548). Accepted (HB ≤ 1.5×).
- Tried: `rw [← map_…]; simpa using ⟨_, hpath, rfl⟩` (works, 1099 HB — over the gate);
  `grind [support_map]` (fails: `PFunctor.FreeM.map` is not syntactically `<$>`, so the
  `support_map` e-match pattern does not fire); `rw … ; simp only [support_map]` (no progress, same
  reason); `support_map ..` (stuck instance: monad not determined).
- What shortened it: term-mode `eq ▸ (support_map _ _).ge ⟨_, hpath, rfl⟩` — the `.ge` of the
  set equation applied to an image witness, with the defeq `FreeM.map = (<$>)` absorbed by
  `exact`-style unification.
- Missing:
  - `mem_support_map_of_mem : x ∈ support mx → f x ∈ support (f <$> mx)` (generic
    `MonadAttach`/`ExactMonadAttach`), would make it `… ▸ mem_support_map_of_mem hpath`.
  - A `support_map` variant (or simp/grind normal form) stated for `PFunctor.FreeM.map`
    (or a `@[simp] FreeM.map f x = f <$> x` bridge) so `simp`/`grind` can see through it.

## B
- Minutes: ~1. B = A + `VCVio.ProgramLogic.Library` import: 5 lines / 577 HB (A 5 / 574).
- Library lemmas used: none. The support calculus (`mem_support_simulateQ_run_*`, the support
  layer of `simulateQ_nf`) is about `simulateQ` runs; the gap here is `PFunctor.FreeM.map`
  vs `<$>`. Missing: `support`/`mem_support` rules (or a `simulateQ_nf`/simp bridge
  `FreeM.map f x = f <$> x`) for `PFunctor.FreeM.map`, and
  `mem_support_map_of_mem : x ∈ support mx → f x ∈ support (f <$> mx)`.
