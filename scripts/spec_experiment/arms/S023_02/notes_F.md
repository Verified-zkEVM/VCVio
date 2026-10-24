# S023_02 `chainInCache_of_mem_support_verifyOpening` (arm F)

- Minutes: ~2.
- Final: 12 lines / 337 HB (original 20 / 309; HB ratio 1.09). ok=true.
- Proof: `simp only [verifyOpening, simulateQ_nf, eq_comm (a := true), beq_iff_eq] at hmem`,
  `obtain ⟨⟨_, _⟩, h, rfl, rfl⟩ := hmem`, then the existing `chainInCache_of_mem_support_getPutativeRoot`.
- Library that helped: the `simulateQ_nf` simp set (simulateQ/StateT run normal form plus support
  unfolding) replaced `rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff]`, the second
  `simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff, Prod.mk.injEq]`, the
  `beq` `have` and the `subst` (~6 lines saved, all of the proof that could be saved).
- Expected but not needed: `mem_support_simulateQ_run_bind_iff` would also work, but the simp set is shorter.
- Friction: `Prod.mk.injEq` leaves `true = (x == root)`, so `eq_comm (a := true)` had to be named.
  A `true = b ↔ b = true` normal form (or `beq` orientation) in `simulateQ_nf` would remove it.
- Missing lemma: none needed.
