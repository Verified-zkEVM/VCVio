/-
Copyright (c) 2026 XC0R, Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R, Quang Dao
-/

module
public import Init.Internal.Order.While
public import LatticeCrypto.Ring.NTTSplitCert

/-!
# In-Place Butterfly Loops As Blocked Stages

This module proves that the in-place radix-2 NTT loops of FIPS 204 Algorithms 41 and 42 compute
the blocked butterfly stages of `LatticeCrypto.Ring.NTTCert`. The loops have the shape

```
while len ≥ 1 do                       -- inverse: while len ≤ N / 2, len := 1, 2, 4, …
  start := 0
  while start < N do
    z := tw k; k := k + 1              -- inverse: z := -tw k; k := k - 1
    for j in [start : start + len] do (butterfly at j and j + len)
    start := start + 2 * len
  len := len / 2                        -- inverse: len := len * 2
```

over an array of size `N = 2^logn` and a twiddle lookup `tw : ℕ → R`. Layer `s` uses
`tw (2^s + g)` for block `g`, and the inverse reads `-tw (2^(s+1) - 1 - g)` for the same block.
`ctStage hk hN tw htw` packages layer `s` of the first `k ≤ logn` layers as a `ScaledStage` on
`ctLayout`.

`ctForward_loop` and `ctInverse_loop` identify the outer loops, written with
`ctForwardBody` / `ctInverseBody`, with `forwardStages` / `inverseStages` of `List.ofFn ctStage`.
`scale_loop` identifies the final normalization loop with `scaleCoeffs`. A concrete scheme proves
its loop definition equal to these bodies by `rfl` against the elaborated `while` loops, then
reads off the transform laws from the stage certificates.

FIPS 203 Algorithms 9 and 10 run only the first `k` layers, as `for` loops over the block indices
and an explicit list of layer lengths. `rangeLayer` is one such layer as a fold, and
`ctForward_range` / `ctInverse_range` identify the folds over the `k` layer lengths with
`forwardStages` / `inverseStages` of the truncated `List.ofFn ctStage`.

The proofs reason about `while` through `Lean.Loop.forIn_eq_of_monadTail`
(`Init.Internal.Order.While`), and about `for` over a range through `forIn_range_pure`.
-/

public section

namespace LatticeCrypto.NTTCert

variable {R : Type}

/-! ## Loop combinators -/

/-- A `for` loop over `[start : stop]` with a pure body is a left fold over `List.range'`. -/
theorem forIn_range_pure {β : Type} (start stop : ℕ) (b : β) (f : β → ℕ → β) :
    forIn (m := Id) [start : stop] b (fun j b => pure (.yield (f b j))) =
      pure (List.foldl f b (List.range' start (stop - start))) := by
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl,
    Std.Legacy.Range.size, Nat.add_sub_cancel, Nat.div_one]

/-- A `while` loop through the states `S 0, …, S n` that stops at `S n`. -/
theorem forIn_loop_eq {σ : Type} {body : Unit → σ → Id (ForInStep σ)} {n : ℕ} (S : ℕ → σ)
    (hstep : ∀ i < n, body () (S i) = pure (.yield (S (i + 1))))
    (hdone : body () (S n) = pure (.done (S n))) :
    forIn Lean.Loop.mk (S 0) body = pure (S n) := by
  have hu (b : σ) : forIn Lean.Loop.mk b body = (do
      match ← body () b with
      | .done b => pure b
      | .yield b => forIn Lean.Loop.mk b body) :=
    Lean.Loop.forIn_eq_of_monadTail
  refine Nat.decreasingInduction (motive := fun i _ => forIn Lean.Loop.mk (S i) body = pure (S n))
    (fun i hi ih => ?_) ?_ n.zero_le
  · rw [hu, hstep i hi]
    exact ih
  · rw [hu, hdone]
    rfl

/-! ## Arrays as coefficient functions

An array of size `N` stands for the coefficient function it reads through `getD`. -/

/-- Reading `Array.ofFn y` through `getD` is `coeffAt y`. -/
theorem getD_ofFn_eq_coeffAt [CommRing R] {N : ℕ} (y : Fin N → R) (i : ℕ) :
    (Array.ofFn y).getD i 0 = coeffAt y i := by
  by_cases h : i < N <;> simp [h, coeffAt_of_lt, coeffAt_of_le, Nat.le_of_not_lt]

/-- The array of a vector is the array of its entries. -/
theorem vector_toArray_eq_ofFn {N : ℕ} (v : Vector R N) :
    v.toArray = Array.ofFn fun i => v.get i :=
  (congrArg Vector.toArray (Vector.ofFn_getElem (xs := v))).symm

private theorem getD_set! [CommRing R] (a : Array R) (p i : ℕ) (v : R) :
    (a.set! p v).getD i 0 = if p = i ∧ p < a.size then v else a.getD i 0 := by
  by_cases h : p = i
  · subst h
    by_cases hp : p < a.size <;> simp [hp]
  · simp [h]

private theorem eq_ofFn [CommRing R] {N : ℕ} {a : Array R} {y : Fin N → R} (hs : a.size = N)
    (h : ∀ i : Fin N, a.getD i 0 = y i) : a = Array.ofFn y := by
  refine Array.ext (by simp [hs]) fun i h1 _ => ?_
  simpa [h1] using h ⟨i, hs ▸ h1⟩

/-! ## Partial layers

`blockPartial x F len start r` is the state after the butterflies of the first `r` offsets of the
block at `start`, with all earlier blocks done: it agrees with the layer output `F` there and with
the layer input `x` elsewhere. -/

private def blockPartial {N : ℕ} (x F : Fin N → R) (len start r : ℕ) : Fin N → R :=
  fun i => if i.val < start + r ∨ start + len ≤ i.val ∧ i.val < start + len + r then F i else x i

private theorem coeffAt_blockPartial [CommRing R] {N : ℕ} (x F : Fin N → R) (len start r i : ℕ) :
    coeffAt (blockPartial x F len start r) i =
      if i < start + r ∨ start + len ≤ i ∧ i < start + len + r then coeffAt F i
      else coeffAt x i := by
  by_cases h : i < N <;> simp [h, coeffAt_of_lt, coeffAt_of_le, Nat.le_of_not_lt, blockPartial]

private theorem blockPartial_zero {N : ℕ} (x F : Fin N → R) (len : ℕ) :
    blockPartial x F len 0 0 = x := by
  funext i
  exact ite_eq_right (by omega)

private theorem blockPartial_len {N : ℕ} (x F : Fin N → R) (len start : ℕ) :
    blockPartial x F len start len = blockPartial x F len (start + 2 * len) 0 := by
  funext i
  simp only [blockPartial]
  split_ifs <;> first | rfl | omega

private theorem blockPartial_end {N len start r : ℕ} (x F : Fin N → R) (h : N ≤ start + r) :
    blockPartial x F len start r = F := by
  funext i
  exact ite_eq_left (Or.inl (by omega))

/-- A left fold over `[0, n)` through the states `S 0, …, S n`. -/
private theorem foldl_range'_states {α : Type} (step : α → ℕ → α) (S : ℕ → α) :
    ∀ n, (∀ i < n, step (S i) i = S (i + 1)) → (List.range' 0 n).foldl step (S 0) = S n
  | 0, _ => rfl
  | n + 1, h => by
    rw [List.range'_1_concat, List.foldl_append,
      foldl_range'_states step S n fun i hi => h i (by omega), List.foldl_cons, List.foldl_nil,
      Nat.zero_add, h n (by omega)]

/-! ## Butterflies -/

/-- The forward butterfly at `j` and `j + len`: `(u, v) ↦ (u + z·v, u − z·v)`. -/
@[expose] def fwdBfly [CommRing R] (z : R) (len : ℕ) (b : Array R) (j : ℕ) : Array R :=
  (b.set! (j + len) (b.getD j 0 - z * b.getD (j + len) 0)).set! j
    (b.getD j 0 + z * b.getD (j + len) 0)

/-- The inverse butterfly at `j` and `j + len`: `(u, v) ↦ (u + v, z·(u − v))`. -/
@[expose] def invBfly [CommRing R] (z : R) (len : ℕ) (b : Array R) (j : ℕ) : Array R :=
  (b.set! j (b.getD j 0 + b.getD (j + len) 0)).set! (j + len)
    (z * (b.getD j 0 - b.getD (j + len) 0))

/-- A butterfly at `start + r` takes the partial state at `r` to the one at `r + 1`. -/
private theorem bfly_eq [CommRing R] {N len start r : ℕ} {z : R} {x F : Fin N → R}
    (hN : start + 2 * len ≤ N) (hr : r < len) :
    let u := coeffAt x (start + r)
    let v := coeffAt x (start + len + r)
    let b := Array.ofFn (blockPartial x F len start r)
    (coeffAt F (start + r) = u + z * v → coeffAt F (start + len + r) = u - z * v →
      fwdBfly z len b (start + r) = Array.ofFn (blockPartial x F len start (r + 1))) ∧
    (coeffAt F (start + r) = u + v → coeffAt F (start + len + r) = z * (u - v) →
      invBfly z len b (start + r) = Array.ofFn (blockPartial x F len start (r + 1))) := by
  have hu := coeffAt_blockPartial x F len start r (start + r)
  have hv := coeffAt_blockPartial x F len start r (start + len + r)
  rw [ite_eq_right (by omega)] at hu hv
  dsimp only
  constructor <;> intro hlo hhi
  all_goals
    simp only [fwdBfly, invBfly, Nat.add_right_comm start r len, getD_ofFn_eq_coeffAt, hu, hv,
      ← hlo, ← hhi]
    refine eq_ofFn (by simp) fun i => ?_
    rw [← coeffAt_fin (blockPartial x F len start (r + 1))]
    simp only [getD_set!, getD_ofFn_eq_coeffAt, Array.size_set!, Array.size_ofFn,
      coeffAt_blockPartial]
    split_ifs <;> first | rfl | omega | (congr 1; omega)

/-! ## Loop bodies -/

/-- The body of the middle `while start < N` loop: the block at `start`, butterflies `bf k` at
`j` and `j + len` for `j ∈ [start, start + len)`; then `k` becomes `kstep k`. -/
@[expose] def loopMidBody (N len : ℕ) (bf : ℕ → Array R → ℕ → Array R) (kstep : ℕ → ℕ)
    (_ : Unit) (st : Array R × ℕ × ℕ) : Id (ForInStep (Array R × ℕ × ℕ)) :=
  if st.2.2 < N then do
    let a ← forIn [st.2.2 : st.2.2 + len] st.1 fun j b => pure (.yield (bf st.2.1 b j))
    pure (.yield (a, kstep st.2.1, st.2.2 + 2 * len))
  else pure (.done st)

/-- The body of the outer `while` loop: while `cond len`, a layer of blocks of `2 * len`
coefficients, butterflies `bf len k` at distance `len`; then `len` becomes `lstep len`. -/
@[expose] def loopOuterBody (N : ℕ) (cond : ℕ → Prop) [DecidablePred cond]
    (bf : ℕ → ℕ → Array R → ℕ → Array R) (kstep lstep : ℕ → ℕ) (_ : Unit)
    (st : Array R × ℕ × ℕ) : Id (ForInStep (Array R × ℕ × ℕ)) :=
  if cond st.2.2 then do
    let st' ← forIn Lean.Loop.mk (st.1, st.2.1, 0) (loopMidBody N st.2.2 (bf st.2.2) kstep)
    pure (.yield (st'.1, st'.2.1, lstep st.2.2))
  else pure (.done st)

/-- The body of the outer loop of the forward transform (FIPS 204 Algorithm 41). -/
@[expose] def ctForwardBody [CommRing R] (N : ℕ) (tw : ℕ → R) :
    Unit → Array R × ℕ × ℕ → Id (ForInStep (Array R × ℕ × ℕ)) :=
  loopOuterBody N (· ≥ 1) (fun len k => fwdBfly (tw k) len) (· + 1) (· / 2)

/-- The body of the outer loop of the inverse transform (FIPS 204 Algorithm 42), before the final
scaling. -/
@[expose] def ctInverseBody [CommRing R] (N : ℕ) (tw : ℕ → R) :
    Unit → Array R × ℕ × ℕ → Id (ForInStep (Array R × ℕ × ℕ)) :=
  loopOuterBody N (· ≤ N / 2) (fun len k => invBfly (-tw k) len) (· - 1) (· * 2)

private theorem midBody_loop {N len G : ℕ} (hG : G * (2 * len) = N) (hlen : 0 < len)
    {bf : ℕ → Array R → ℕ → Array R} {kstep kOf : ℕ → ℕ} (x F : Fin N → R)
    (hbf : ∀ g < G, ∀ r < len, g * (2 * len) + 2 * len ≤ N →
      bf (kOf g) (Array.ofFn (blockPartial x F len (g * (2 * len)) r)) (g * (2 * len) + r) =
        Array.ofFn (blockPartial x F len (g * (2 * len)) (r + 1)))
    (hk : ∀ g < G, kstep (kOf g) = kOf (g + 1)) :
    forIn Lean.Loop.mk (Array.ofFn x, kOf 0, 0) (loopMidBody N len bf kstep) =
      (pure (Array.ofFn F, kOf G, N) : Id _) := by
  have h := forIn_loop_eq (n := G) (body := loopMidBody N len bf kstep)
    (fun g => (Array.ofFn (blockPartial x F len (g * (2 * len)) 0), kOf g, g * (2 * len)))
    (fun g hg => by
      have hle : g * (2 * len) + 2 * len ≤ N := by
        rw [← hG, ← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hg
      have hin := foldl_range'_states (fun b r => bf (kOf g) b (g * (2 * len) + r))
        (fun r => Array.ofFn (blockPartial x F len (g * (2 * len)) r)) len
        (fun r hr => hbf g hg r hr hle)
      beta_reduce at hin
      simp only [loopMidBody, show g * (2 * len) < N by omega, ite_true, forIn_range_pure,
        Nat.add_sub_cancel_left, pure_bind]
      rw [show List.range' (g * (2 * len)) len = (List.range' 0 len).map (g * (2 * len) + ·) by
          rw [List.map_add_range', Nat.add_zero],
        List.foldl_map, hin, blockPartial_len, hk g hg, Nat.add_one_mul g])
    (by simp only [loopMidBody, hG, lt_irrefl, ite_false])
  simpa only [Nat.zero_mul, blockPartial_zero, hG, blockPartial_end x F (Nat.le_add_right N 0)]
    using h

/-- The outer loop through the layer states `(Y i, K i, L i)` for `i ≤ n`. -/
private theorem outer_loop {N n : ℕ} {cond : ℕ → Prop} [DecidablePred cond]
    {bf : ℕ → ℕ → Array R → ℕ → Array R} {kstep lstep : ℕ → ℕ}
    (Y : ℕ → Fin N → R) (K L : ℕ → ℕ) {a : Array R} {y : Fin N → R}
    (ha : a = Array.ofFn (Y 0)) (hy : Y n = y)
    (hmid : ∀ i < n, forIn Lean.Loop.mk (Array.ofFn (Y i), K i, 0)
      (loopMidBody N (L i) (bf (L i)) kstep) = pure (Array.ofFn (Y (i + 1)), K (i + 1), N))
    (hcond : ∀ i ≤ n, cond (L i) ↔ i < n) (hL : ∀ i < n, lstep (L i) = L (i + 1)) :
    (Id.run (forIn Lean.Loop.mk (a, K 0, L 0) (loopOuterBody N cond bf kstep lstep))).1 =
      Array.ofFn y := by
  subst ha hy
  rw [forIn_loop_eq (n := n) (fun i => (Array.ofFn (Y i), K i, L i))
    (fun i hi => by
      simp only [loopOuterBody, (hcond i hi.le).2 hi, ite_true, hmid i hi, pure_bind, hL i hi])
    (by
      simp only [loopOuterBody, (hcond n le_rfl).trans (iff_false_intro (lt_irrefl n)),
        ite_false])]
  rfl

/-! ## Stages -/

/-- Layer `s` of a transform of size `2^logn` has `2^s` blocks of `2 · 2^(logn - 1 - s)`
coefficients. -/
theorem ctLayer_shape (logn : ℕ) (s : Fin logn) :
    2 ^ s.val * (2 * 2 ^ (logn - 1 - s.val)) = 2 ^ logn := by
  rw [← pow_succ', ← pow_add]
  congr 1
  omega

/-- Layer `s` of the first `k` of the `logn` layers as a stage on `ctLayout`: `2^s` blocks of
`2^(logn - s)` coefficients, with the forward twiddles `tw (2^s + g)` and the inverse twiddles
`-tw (2^(s+1) - 1 - g)`. -/
@[expose] def ctStage [CommRing R] {k logn N : ℕ} (hk : k ≤ logn) (hN : 2 ^ logn = N)
    (tw : ℕ → R)
    (htw : ∀ (s : Fin k) (g : Fin (2 ^ s.val)),
      -tw (2 ^ (s.val + 1) - 1 - g.val) * tw (2 ^ s.val + g.val) = 1)
    (s : Fin k) : ScaledStage R (Fin N) :=
  butterflyStage (ctLayout (2 ^ s.val) (2 ^ (logn - 1 - s.val))
      ((ctLayer_shape logn (Fin.castLE hk s)).trans hN))
    (fun pair => tw (2 ^ s.val + pair.1.val))
    (fun pair => -tw (2 ^ (s.val + 1) - 1 - pair.1.val))
    (fun pair => htw s pair.1)

/-! ## Loops as stages -/

/-- The forward loop computes `forwardStages` of the `ctStage` layers. -/
theorem ctForward_loop [CommRing R] {logn N : ℕ} (hN : 2 ^ logn = N) (tw : ℕ → R)
    (htw : ∀ (s : Fin logn) (g : Fin (2 ^ s.val)),
      -tw (2 ^ (s.val + 1) - 1 - g.val) * tw (2 ^ s.val + g.val) = 1)
    {a : Array R} {y : Fin N → R} (ha : a = Array.ofFn y) :
    (Id.run (forIn Lean.Loop.mk (a, 1, N / 2) (ctForwardBody N tw))).1 =
      Array.ofFn (forwardStages (List.ofFn (ctStage le_rfl hN tw htw)) y) := by
  subst hN
  exact outer_loop (n := logn)
    (fun s => forwardStages ((List.ofFn (ctStage le_rfl rfl tw htw)).take s) y)
    (2 ^ ·) (fun s => 2 ^ logn / 2 ^ (s + 1)) ha
    (congrArg (forwardStages · _) (List.take_of_length_le List.length_ofFn.le))
    (fun s hs => by
      have hG := ctLayer_shape logn ⟨s, hs⟩
      let z (g : Fin (2 ^ s)) := tw (2 ^ s + g.val)
      rw [show 2 ^ logn / 2 ^ (s + 1) = 2 ^ (logn - 1 - s) by
          rw [Nat.pow_div (by omega) two_pos]; congr 1; omega,
        List.take_add_one, List.getElem?_ofFn, dite_eq_left hs, Option.toList_some,
        forwardStages_append, pow_succ, mul_two]
      exact midBody_loop hG (by positivity) (kOf := (2 ^ s + ·)) _ _ (fun g hg r hr hN =>
        (bfly_eq hN hr).1 (coeffAt_forwardStage_ctLayout_left hG z _ ⟨g, hg⟩ hr)
          (coeffAt_forwardStage_ctLayout_right hG z _ ⟨g, hg⟩ hr)) fun _ _ => Nat.add_assoc _ _ _)
    (fun s _ => by
      rw [ge_iff_le, Nat.one_le_div_iff (Nat.two_pow_pos _), Nat.pow_le_pow_iff_right one_lt_two]
      omega)
    fun s _ => by rw [Nat.div_div_eq_div_mul, ← pow_succ]

/-- The inverse loop, before scaling, computes `inverseStages` of the `ctStage` layers. -/
theorem ctInverse_loop [CommRing R] {logn N : ℕ} (hN : 2 ^ logn = N) (tw : ℕ → R)
    (htw : ∀ (s : Fin logn) (g : Fin (2 ^ s.val)),
      -tw (2 ^ (s.val + 1) - 1 - g.val) * tw (2 ^ s.val + g.val) = 1)
    {a : Array R} {y : Fin N → R} (ha : a = Array.ofFn y) :
    (Id.run (forIn Lean.Loop.mk (a, N - 1, 1) (ctInverseBody N tw))).1 =
      Array.ofFn (inverseStages (List.ofFn (ctStage le_rfl hN tw htw)) y) := by
  subst hN
  exact outer_loop (n := logn)
    (fun i => inverseStages ((List.ofFn (ctStage le_rfl rfl tw htw)).drop (logn - i)) y)
    (fun i => 2 ^ (logn - i) - 1) (2 ^ ·)
    (ha.trans (by rw [Nat.sub_zero, List.drop_of_length_le List.length_ofFn.le]; rfl))
    (by rw [Nat.sub_self]; rfl)
    (fun i hi => by
      obtain ⟨s, hs, rfl⟩ : ∃ s, s < logn ∧ i = logn - 1 - s := ⟨logn - 1 - i, by omega, by omega⟩
      have hG := ctLayer_shape logn ⟨s, hs⟩
      let z (g : Fin (2 ^ s)) := -tw (2 ^ (s + 1) - 1 - g.val)
      rw [show logn - (logn - 1 - s) = s + 1 by omega, show logn - (logn - 1 - s + 1) = s by omega,
        List.drop_eq_getElem_cons (i := s) (by simpa using hs), List.getElem_ofFn,
        show 2 ^ s - 1 = 2 ^ (s + 1) - 1 - 2 ^ s by rw [pow_succ]; omega]
      exact midBody_loop hG (by positivity) (kOf := (2 ^ (s + 1) - 1 - ·)) _ _ (fun g hg r hr hN =>
        (bfly_eq hN hr).2 (coeffAt_inverseStage_ctLayout_left hG z _ ⟨g, hg⟩ hr)
          (coeffAt_inverseStage_ctLayout_right hG z _ ⟨g, hg⟩ hr)) fun _ _ => Nat.sub_sub _ _ _)
    (fun i _ => by
      rw [Nat.le_div_iff_mul_le two_pos, ← pow_succ, Nat.pow_le_pow_iff_right one_lt_two]
      omega)
    fun i _ => (pow_succ 2 i).symm

/-! ## Range-loop layers

FIPS 203 Algorithms 9 and 10 write a layer as range loops over its blocks and the offsets in a
block, run the layers over an explicit list of butterfly distances, and stop after the first `k`
of the `logn` layers. -/

/-- One layer in range-loop form at butterfly distance `len`: for each block `g < N / (2 * len)`,
the butterflies `bf len k` at `g * 2 * len + jj` for `jj < len`; then `k` becomes `kstep k`. -/
@[expose] def rangeLayer (N : ℕ) (bf : ℕ → ℕ → Array R → ℕ → Array R) (kstep : ℕ → ℕ)
    (st : Array R × ℕ) (len : ℕ) : Array R × ℕ :=
  (List.range' 0 (N / (2 * len))).foldl
    (fun st g => ((List.range' 0 len).foldl (fun b jj => bf len st.2 b (g * 2 * len + jj)) st.1,
      kstep st.2)) st

private theorem rangeLayer_eq {N len G : ℕ} (hG : G * (2 * len) = N) (hlen : 0 < len)
    {bf : ℕ → ℕ → Array R → ℕ → Array R} {kstep kOf : ℕ → ℕ} (x F : Fin N → R)
    (hbf : ∀ g < G, ∀ r < len, g * (2 * len) + 2 * len ≤ N →
      bf len (kOf g) (Array.ofFn (blockPartial x F len (g * (2 * len)) r)) (g * (2 * len) + r) =
        Array.ofFn (blockPartial x F len (g * (2 * len)) (r + 1)))
    (hk : ∀ g < G, kstep (kOf g) = kOf (g + 1)) :
    rangeLayer N bf kstep (Array.ofFn x, kOf 0) len = (Array.ofFn F, kOf G) := by
  have h := foldl_range'_states
    (fun st g => ((List.range' 0 len).foldl (fun b jj => bf len st.2 b (g * 2 * len + jj)) st.1,
      kstep st.2))
    (fun g => (Array.ofFn (blockPartial x F len (g * (2 * len)) 0), kOf g)) G (fun g hg => by
      have hle : g * (2 * len) + 2 * len ≤ N := by
        rw [← hG, ← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hg
      have hin := foldl_range'_states (fun b r => bf len (kOf g) b (g * (2 * len) + r))
        (fun r => Array.ofFn (blockPartial x F len (g * (2 * len)) r)) len
        (fun r hr => hbf g hg r hr hle)
      beta_reduce at hin ⊢
      simp only [Nat.mul_assoc g 2 len, hin, blockPartial_len, hk g hg, Nat.add_one_mul g])
  beta_reduce at h
  rw [rangeLayer, show N / (2 * len) = G by rw [← hG, Nat.mul_div_cancel _ (by omega)]]
  simpa only [Nat.zero_mul, blockPartial_zero, hG, blockPartial_end x F (Nat.le_add_right N 0)]
    using h

/-- The first `k` forward layers in range-loop form, at distances `2^(logn - 1), …, 2^(logn - k)`
with the twiddle index counting up from `1`, compute `forwardStages` of the `ctStage` layers. -/
theorem ctForward_range [CommRing R] {k logn N : ℕ} (hk : k ≤ logn) (hN : 2 ^ logn = N)
    (tw : ℕ → R)
    (htw : ∀ (s : Fin k) (g : Fin (2 ^ s.val)),
      -tw (2 ^ (s.val + 1) - 1 - g.val) * tw (2 ^ s.val + g.val) = 1)
    {a : Array R} {y : Fin N → R} (ha : a = Array.ofFn y) :
    (((List.range' 0 k).map fun s => 2 ^ (logn - 1 - s)).foldl
      (rangeLayer N (fun len k => fwdBfly (tw k) len) (· + 1)) (a, 1)).1 =
      Array.ofFn (forwardStages (List.ofFn (ctStage hk hN tw htw)) y) := by
  subst hN ha
  rw [List.foldl_map]
  have h := foldl_range'_states
    (fun st s => rangeLayer (2 ^ logn) (fun len k => fwdBfly (tw k) len) (· + 1) st
      (2 ^ (logn - 1 - s)))
    (fun s => (Array.ofFn (forwardStages ((List.ofFn (ctStage hk rfl tw htw)).take s) y), 2 ^ s))
    k (fun s hs => by
      have hG := ctLayer_shape logn ⟨s, by omega⟩
      let z (g : Fin (2 ^ s)) := tw (2 ^ s + g.val)
      rw [List.take_add_one, List.getElem?_ofFn, dite_eq_left hs, Option.toList_some,
        forwardStages_append, pow_succ, mul_two]
      exact rangeLayer_eq hG (by positivity) (kOf := (2 ^ s + ·)) _ _ (fun g hg r hr hN =>
        (bfly_eq hN hr).1 (coeffAt_forwardStage_ctLayout_left hG z _ ⟨g, hg⟩ hr)
          (coeffAt_forwardStage_ctLayout_right hG z _ ⟨g, hg⟩ hr)) fun _ _ => Nat.add_assoc _ _ _)
  beta_reduce at h
  rw [show (Array.ofFn y, 1) = (Array.ofFn (forwardStages
      ((List.ofFn (ctStage hk rfl tw htw)).take 0) y), 2 ^ 0) from rfl, h,
    List.take_of_length_le List.length_ofFn.le]

/-- The first `k` inverse layers in range-loop form, before scaling, at distances
`2^(logn - k), …, 2^(logn - 1)` with the twiddle index counting down from `2^k - 1`, compute
`inverseStages` of the `ctStage` layers. -/
theorem ctInverse_range [CommRing R] {k logn N : ℕ} (hk : k ≤ logn) (hN : 2 ^ logn = N)
    (tw : ℕ → R)
    (htw : ∀ (s : Fin k) (g : Fin (2 ^ s.val)),
      -tw (2 ^ (s.val + 1) - 1 - g.val) * tw (2 ^ s.val + g.val) = 1)
    {a : Array R} {y : Fin N → R} (ha : a = Array.ofFn y) :
    (((List.range' 0 k).map fun i => 2 ^ (logn - k + i)).foldl
      (rangeLayer N (fun len k => invBfly (-tw k) len) (· - 1)) (a, 2 ^ k - 1)).1 =
      Array.ofFn (inverseStages (List.ofFn (ctStage hk hN tw htw)) y) := by
  subst hN ha
  rw [List.foldl_map]
  have h := foldl_range'_states
    (fun st i => rangeLayer (2 ^ logn) (fun len k => invBfly (-tw k) len) (· - 1) st
      (2 ^ (logn - k + i)))
    (fun i => (Array.ofFn (inverseStages ((List.ofFn (ctStage hk rfl tw htw)).drop (k - i)) y),
      2 ^ (k - i) - 1))
    k (fun i hi => by
      obtain ⟨s, hs, rfl⟩ : ∃ s, s < k ∧ i = k - 1 - s := ⟨k - 1 - i, by omega, by omega⟩
      have hG := ctLayer_shape logn ⟨s, by omega⟩
      let z (g : Fin (2 ^ s)) := -tw (2 ^ (s + 1) - 1 - g.val)
      rw [show k - (k - 1 - s) = s + 1 by omega, show k - (k - 1 - s + 1) = s by omega,
        show logn - k + (k - 1 - s) = logn - 1 - s by omega,
        List.drop_eq_getElem_cons (i := s) (by simpa using hs), List.getElem_ofFn,
        show 2 ^ s - 1 = 2 ^ (s + 1) - 1 - 2 ^ s by rw [pow_succ]; omega]
      exact rangeLayer_eq hG (by positivity) (kOf := (2 ^ (s + 1) - 1 - ·)) _ _
        (fun g hg r hr hN =>
          (bfly_eq hN hr).2 (coeffAt_inverseStage_ctLayout_left hG z _ ⟨g, hg⟩ hr)
            (coeffAt_inverseStage_ctLayout_right hG z _ ⟨g, hg⟩ hr)) fun _ _ => Nat.sub_sub _ _ _)
  beta_reduce at h
  rw [show (Array.ofFn y, 2 ^ k - 1) = (Array.ofFn (inverseStages
      ((List.ofFn (ctStage hk rfl tw htw)).drop (k - 0)) y), 2 ^ (k - 0) - 1) by
    rw [Nat.sub_zero, List.drop_of_length_le List.length_ofFn.le]; rfl, h, Nat.sub_self]
  rfl

/-- The final normalization loop multiplies every coefficient by `c`. -/
theorem scale_loop [CommRing R] {N : ℕ} (c : R) (y : Fin N → R) :
    Id.run (forIn [0 : N] (Array.ofFn y) fun j b => pure (.yield (b.set! j (c * b.getD j 0)))) =
      Array.ofFn (scaleCoeffs c y) := by
  rw [forIn_range_pure, Nat.sub_zero]
  have h := foldl_range'_states (fun b j => b.set! j (c * b.getD j 0))
    (fun r => Array.ofFn (blockPartial y (scaleCoeffs c y) N 0 r)) N (fun r hr => by
      refine eq_ofFn (by simp) fun i => ?_
      rw [← coeffAt_fin (blockPartial y _ N 0 (r + 1))]
      simp only [getD_set!, getD_ofFn_eq_coeffAt, coeffAt_blockPartial, coeffAt_scaleCoeffs,
        Array.size_ofFn, Nat.zero_add]
      split_ifs <;> first | rfl | omega | (congr 2; omega))
  beta_reduce at h
  rwa [blockPartial_zero, blockPartial_end _ _ (Nat.zero_add N).ge] at h

end LatticeCrypto.NTTCert
