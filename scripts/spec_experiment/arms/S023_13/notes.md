# S023_13 prEvent_contextForkPair_le_guarded_add_collision — arm A

- Minutes: ~8
- Result: 11 lines / 789 HB (original 33 / 1370). Accepted.
- Tried: unfolding all three experiments to `<$>` over the shared fork view
  (`rw [… filterMapLocateAndForkAt, contextForkViewCollision, FreeM.map_eq_map ×2]; simp only
  [prEvent_map]`, works, 973 HB, 7 lines); `congrArg₂ _ (prEvent_map _ _ _).symm (prEvent_map _
  _ _).symm` with all arguments inferred (fails for the collision event: higher-order unification
  `?p (?f x) =?= (collide x = some s)` needs the event `(· = some s)` given).
- What shortened it: no named intermediate predicates/`have`s — `prEvent_mono` with the union's
  predicates inferred from `prEvent_or_le`, and the two "event of a mapped computation" identities
  closed by `prEvent_map` up to the defeq `FreeM.map = (<$>)`; the pointwise case split is one
  `rcases … <;> simp; grind [classifyForkView, collideForkView]`.
- Missing:
  - A union-bound-through-maps lemma: `Pr[p (f x) | mx] ≤ Pr[q (g x) | mx] + Pr[r (h x) | mx]`
    stated as `(∀ x, p (f x) → q (g x) ∨ r (h x)) → Pr[p | f <$> mx] ≤ Pr[q | g <$> mx] +
    Pr[r | h <$> mx]` (three experiments that are maps of one source computation — a recurring
    shape in fork/collision splits).
  - `prEvent_map` variant (or simp normal form) for `PFunctor.FreeM.map` so that `simp only
    [prEvent_map]` fires without first rewriting `FreeM.map_eq_map` (the same gap as S023_01).

## B
- Minutes: ~2. B = A + import: 11 lines / 809 HB (A 11 / 789).
- Looked at T1/ProbBounds (`prEvent_bind_le_add_iSup`, the `prEvent_*_bind_le_add` family):
  all are bounds through a *bind*; this proof is a union bound over three *maps* of one source.
  Missing: `(∀ x, p (f x) → q (g x) ∨ r (h x)) →
    Pr[p | f <$> mx] ≤ Pr[q | g <$> mx] + Pr[r | h <$> mx]`, and `prEvent_map` for
  `PFunctor.FreeM.map`.
