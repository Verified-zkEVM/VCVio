# S023_13 `prEvent_contextForkPair_le_guarded_add_collision` (arm F)

- Minutes: ~3.
- Final: 12 lines / 964 HB (original 33 / 1370). ok=true.
- Proof: `rw [contextForkPair, observedForkPair, prEvent_map]`, then one `refine` chaining
  `prEvent_mono` → `prEvent_or_le` → `congrArg₂ _ (prEvent_map …).symm (prEvent_map …).symm`
  (the right side unfolds by defeq to maps of `contextForkView`), then the pointwise case
  `rcases v with _ | v <;> grind [classifyForkView, collideForkView]`.
- Library that helped: none. This is a probability partition proved with core `prEvent_*` lemmas.
  ProbBounds (T1) covers binds, uniform draws and stateful runs, but has no
  union/partition-through-a-map rule.
- Tried: plain `grind` with no case split (fails because it needs the `Option` split);
  `simp at hv ⊢ <;> grind` works but trips the unused-`<;>` linter.
- Missing generic lemma (would reduce this to about 3 lines):
  `prEvent_map_le_add_of_imp (mx : m α) (f : α → β) (g : α → γ) (h : α → δ) (p q r)
   (himp : ∀ x, p (f x) → q (g x) ∨ r (h x)) :
   Pr{let y ← f <$> mx}[p y] ≤ Pr{let y ← g <$> mx}[q y] + Pr{let y ← h <$> mx}[r y]`.
