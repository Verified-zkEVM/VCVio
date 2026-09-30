/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio

/-!
# Probability tactic gate

Families of outcome, event, success-mass and distribution facts, stated with `𝒟[…]` and
`Pr{…}[…]` over `ProbComp`, each closed by one terminal tactic under the rules of *Normal forms
and the tactic contract* in `docs/agents/probability.md`. Where a fact closes by both `simp` and
`grind` both are kept; where only one closes, a dated `fail_if_success` guard records the gap and
expires when the set improves. One guard covers a family of same-shaped entries when the family is
named in the section note. Bind-swap and shared-prefix congruence go through `prrw`.

Two gaps recur across the file and are named once here. `grind` does no `ℝ≥0∞` or cardinality
arithmetic and has no measure-side rules for Dirac or uniform masses, so beyond the lossless
event it closes only the symbolic families (equiprobability after a rewrite, pushforward of an
event, structural `bind`/`pure` collapse). Finite counting leaves `#{x | p x} / n` unevaluated;
`simp [Finset.filter_eq']` evaluates singleton filters and `rfl` the rest.
-/

public section

open MeasureTheory ProbabilityTheory OracleComp OracleSpec
open scoped ENNReal

namespace VCVioTest.ProbabilityTactics

/-! ## 1. Outcome masses — `𝒟[mx] {x}`

### Deterministic outcomes
A `pure` computation is the Dirac measure at its value.

gap(simp): a Dirac singleton normalises to `Pi.single x 1 y`, which `simp` does not turn back into
an `if`. -/

example (x : Bool) : 𝒟[(pure x : ProbComp Bool)] {x} = 1 := by
  fail_if_success grind  -- gap(grind, 2026-09-26): Dirac masses, covers the section
  simp
example (x : Bool) : 𝒟[(pure x : ProbComp Bool)] = Measure.dirac x := by simp
example (x : Bool) : 𝒟[(pure x : ProbComp Bool)] {x} ≠ 0 := by simp
example (x : Bool) : Pr{let y ← (pure x : ProbComp Bool)}[y = x] = 1 := by simp

example (x y : Bool) : 𝒟[(pure y : ProbComp Bool)] {x} = if x = y then 1 else 0 := by
  fail_if_success (simp; done)  -- gap(simp, 2026-09-26): stops at `Pi.single y 1 x`
  simp [Pi.single_apply, eq_comm]

/-! ### Uniform draws
Every outcome of a uniform draw over an `n`-element type has mass `1 / n`. `Sum` carries no
`MeasurableSingletonClass` instance, so its outcome is stated as a `Pr{…}` event. -/

example : 𝒟[($ᵗ Bool : ProbComp Bool)] {true} = 2⁻¹ := by
  fail_if_success grind  -- gap(grind, 2026-09-26): concrete values, covers this section
  simp
example : 𝒟[($ᵗ (Fin 6) : ProbComp (Fin 6))] {0} = 6⁻¹ := by simp
example (x : Fin 6) : 𝒟[$ᵗ Fin 6] {x} = 6⁻¹ := by simp
example : 𝒟[($ᵗ Bool : ProbComp Bool)] {true} ≠ 0 := by simp
example : 𝒟[($ᵗ (Fin 3) : ProbComp (Fin 3))] {0} ≠ 0 := by simp
example (x : Bool ⊕ Bool) : Pr{let y ← ($ᵗ (Bool ⊕ Bool) : ProbComp (Bool ⊕ Bool))}[y = x] ≠ 0 := by
  simp

example (x y : Fin 6) :
    𝒟[($ᵗ (Fin 6) : ProbComp (Fin 6))] {x} = 𝒟[($ᵗ (Fin 6) : ProbComp (Fin 6))] {y} := by simp
example (x y : Fin 6) :
    𝒟[($ᵗ (Fin 6) : ProbComp (Fin 6))] {x} = 𝒟[($ᵗ (Fin 6) : ProbComp (Fin 6))] {y} := by grind
example : 𝒟[($ᵗ Bool : ProbComp Bool)] {true} = 𝒟[($ᵗ Bool : ProbComp Bool)] {false} := by simp
example : 𝒟[($ᵗ Bool : ProbComp Bool)] {true} = 𝒟[($ᵗ Bool : ProbComp Bool)] {false} := by grind

example : Pr{let y ← ($ᵗ (ZMod 5) : ProbComp (ZMod 5))}[y = 3] = 5⁻¹ := by
  fail_if_success (simp; done)  -- gap(simp, 2026-09-26): the singleton filter card, see header
  simp [Finset.filter_eq']
example : Pr{let y ← ($ᵗ (BitVec 4) : ProbComp (BitVec 4))}[y = 0] = 16⁻¹ := by
  simp [Finset.filter_eq']

/-! ### Bounds
An outcome mass lies in `[0, 1]` and is never `⊤`. -/

example (mx : ProbComp Bool) (x : Bool) : 𝒟[mx] {x} ≤ 1 := by
  fail_if_success grind  -- gap(grind, 2026-09-26): no measure-side bound rules, covers the section
  simp
example (mx : ProbComp Bool) (x : Bool) : 𝒟[mx] {x} ≠ ⊤ := by simp
example (mx : ProbComp Bool) (x : Bool) : 0 ≤ 𝒟[mx] {x} := by simp

/-! ### `bind`/`pure`-normalised computations -/

example : 𝒟[(do let b ← $ᵗ Bool; pure b : ProbComp Bool)] {true} =
    𝒟[($ᵗ Bool : ProbComp Bool)] {true} := by simp
example : 𝒟[(do let b ← $ᵗ Bool; pure b : ProbComp Bool)] {true} =
    𝒟[($ᵗ Bool : ProbComp Bool)] {true} := by grind
example (mx : ProbComp Bool) (x : Bool) : 𝒟[do let y ← mx; pure y] {x} = 𝒟[mx] {x} := by simp
example (mx : ProbComp Bool) (x : Bool) : 𝒟[do let y ← mx; pure y] {x} = 𝒟[mx] {x} := by grind

example (x : Bool) : 𝒟[(do let _ ← $ᵗ Bool; pure x : ProbComp Bool)] {x} = 1 := by
  fail_if_success grind  -- gap(grind, 2026-09-26): discarding a lossless draw
  simp

-- target(simp): over a discarded `Bool`, Mathlib's `simp` rewrites `(Set.univ : Set Bool)` to
-- `{false, true}` before the lossless-mass rule sees it; the oracle-specific law closes the goal.
example (mx : ProbComp Bool) (my : ProbComp (Fin 3)) : 𝒟[mx >>= fun _ => my] = 𝒟[my] :=
  OracleComp.evalDist_bind_const mx my
example (mx : ProbComp (Fin 2)) (my : ProbComp (Fin 3)) : 𝒟[mx >>= fun _ => my] = 𝒟[my] := by
  simp
example (mx : ProbComp (Fin 2)) (b : Fin 3) : 𝒟[(fun _ => b) <$> mx] = Measure.dirac b := by
  simp

/-! ### Independence and the multiplication rule
Two independent uniform draws factor: the joint mass is the product of the marginals.

gap(simp): the singleton of a product measure is not split into a rectangle, so the factorization
goes through `evalDist_pair` and `Measure.prod_prod` by hand. -/

example (a b : Bool) :
    𝒟[(do let x ← $ᵗ Bool; let y ← $ᵗ Bool; pure (x, y) : ProbComp (Bool × Bool))] {(a, b)} =
      𝒟[($ᵗ Bool : ProbComp Bool)] {a} * 𝒟[($ᵗ Bool : ProbComp Bool)] {b} := by
  fail_if_success (simp; done)  -- gap(simp, 2026-09-26): product singletons, covers the section
  fail_if_success grind  -- gap(grind, 2026-09-26): product singletons, covers the section
  rw [evalDist_pair, ← Set.singleton_prod_singleton, Measure.prod_prod]
example :
    𝒟[(do let x ← $ᵗ (Fin 6); let y ← $ᵗ (Fin 6); pure (x, y) : ProbComp (Fin 6 × Fin 6))]
      {((5 : Fin 6), (5 : Fin 6))} = 6⁻¹ * 6⁻¹ := by
  rw [evalDist_pair, ← Set.singleton_prod_singleton, Measure.prod_prod]
  simp
example (z : Bool × Bool) :
    𝒟[((·, ·) <$> ($ᵗ Bool) <*> ($ᵗ Bool) : ProbComp (Bool × Bool))] {z} =
      𝒟[($ᵗ Bool : ProbComp Bool)] {z.1} * 𝒟[($ᵗ Bool : ProbComp Bool)] {z.2} := by
  rw [evalDist_seq_map_prod_mk, ← Set.singleton_prod_singleton, Measure.prod_prod]

example (f : Bool → ProbComp (Fin 3)) (v : Bool → Fin 3) :
    𝒟[Fintype.mPi f] {v} = ∏ i, 𝒟[f i] {v i} := by
  simp [evalDist_mPi]

/-! ## 2. Event probability — `Pr{…}[…]` -/

/-! ### Bounds and constant events -/

example (mx : ProbComp Bool) (p : Bool → Prop) : Pr{let x ← mx}[p x] ≤ 1 := by
  fail_if_success grind  -- gap(grind, 2026-09-26): no measure-side bound rules
  simp
example (mx : ProbComp Bool) (p : Bool → Prop) : Pr{let x ← mx}[p x] ≠ ⊤ := by simp
example (mx : ProbComp Bool) : Pr{let _ ← mx}[False] = 0 := by simp
example (mx : ProbComp Bool) : Pr{let _ ← mx}[False] = 0 := by grind

/-! ### Counting (favourable / total)
The uniform event law reduces to a filtered cardinality over the sample space, which is left
unevaluated (see the header). -/

example : Pr{let b ← ($ᵗ Bool : ProbComp Bool)}[b = true] = 2⁻¹ := by
  fail_if_success (simp; done)  -- gap(simp, 2026-09-26): counting, covers this section
  fail_if_success grind  -- gap(grind, 2026-09-26): counting, covers this section
  simp [Finset.filter_eq']
example : Pr{let b ← ($ᵗ Bool : ProbComp Bool)}[b ≠ true] = 2⁻¹ := by
  simp [Finset.filter_eq']
example : Pr{let n ← ($ᵗ (Fin 6) : ProbComp (Fin 6))}[n < 3] = 3 / 6 := by
  simp; rfl
example : Pr{let n ← ($ᵗ (Fin 6) : ProbComp (Fin 6))}[n = 0 ∨ n = 1] = 2 / 6 := by
  simp; rfl
example : Pr{let p ← ($ᵗ (Bool × Bool) : ProbComp (Bool × Bool))}[p.1 = true ∨ p.2 = true] =
    3 / 4 := by
  simp; rfl

/-! ### Monotonicity and map pushforward
An event implies a wider event; the event of a map is the pulled-back event. -/

example (mx : ProbComp Bool) (p q : Bool → Prop) (h : ∀ x, p x → q x) :
    Pr{let x ← mx}[p x] ≤ Pr{let x ← mx}[q x] := prEvent_mono mx p q h

example (mx : ProbComp Bool) (q : Fin 6 → Prop) (f : Bool → Fin 6) :
    Pr{let y ← f <$> mx}[q y] = Pr{let x ← mx}[q (f x)] := by simp
example (mx : ProbComp Bool) (q : Fin 6 → Prop) (f : Bool → Fin 6) :
    Pr{let y ← f <$> mx}[q y] = Pr{let x ← mx}[q (f x)] := by grind

/-! ## 3. Success mass
A `ProbComp` is lossless; failure in `OptionT ProbComp` is missing mass. -/

example (x : Bool) : 𝒟[(pure x : ProbComp Bool)] Set.univ = 1 := by
  fail_if_success grind  -- gap(grind, 2026-09-26): losslessness, covers the section
  simp
example : 𝒟[($ᵗ Bool : ProbComp Bool)] Set.univ = 1 := by simp
example : 𝒟[(do let x ← $ᵗ Bool; let y ← $ᵗ Bool; pure (x && y) : ProbComp Bool)] Set.univ =
    1 := by simp
example (mx : ProbComp (Fin 3)) : 𝒟[mx] Set.univ = 1 := by simp
example (mx : ProbComp Bool) : 𝒟[mx] Set.univ ≠ 0 := by simp
example (α : Type) [SampleableType α] : Pr{let _ ← ($ᵗ α : ProbComp α)}[True] = 1 := by simp
example (α : Type) [SampleableType α] : Pr{let _ ← ($ᵗ α : ProbComp α)}[True] ≠ 0 := by simp
example (mx : ProbComp (Fin 3)) : IsProbabilityMeasure 𝒟[mx] := inferInstance

example : Pr{let _ ← ($ᵗ Bool : ProbComp Bool)}[True] = 1 := by simp

/-! ### Selection and abort (`OptionT ProbComp`)
Selecting from the empty list and `failure` carry no successful mass.

gap(simp): the success mass of a selection from a nonempty list stays unevaluated. -/

example : 𝒟[(failure : OptionT ProbComp Bool)] = 0 := by simp
example : 𝒟[(failure : OptionT ProbComp Bool)] = 0 := by grind
example : 𝒟[(($ ([] : List Bool)) : OptionT ProbComp Bool)] = 0 := by simp
example : 𝒟[(($ ([] : List Bool)) : OptionT ProbComp Bool)] = 0 := by grind
example (mx : OptionT ProbComp Bool) :
    𝒟[mx >>= fun _ => (failure : OptionT ProbComp Bool)] = 0 := by simp

example : Pr{let _ ← (($ ([true, false] : List Bool)) : OptionT ProbComp Bool)}[True] = 1 := by
  fail_if_success simp  -- gap(simp, 2026-09-26): no rule reaches the unevaluated selection
  rw [ProbComp.prEvent_uniformSelectList]; simp [ENNReal.div_self]

/-- Selecting from a list counts entries with multiplicity. -/
example : Pr{let x ← ($ ([1, 2, 2] : List ℕ) : OptionT ProbComp ℕ)}[x = 2] = 2 / 3 := by
  rw [ProbComp.prEvent_uniformSelectList]
  norm_num

/-- Selecting from an empty list fails, so its events carry no successful mass. -/
example : Pr{let x ← ($ ([] : List ℕ) : OptionT ProbComp ℕ)}[x = 2] = 0 := by
  rw [ProbComp.prEvent_uniformSelectList]
  simp

/-! ## 4. The support ↔ mass bridge
A value has zero mass exactly when it is outside the support; an event has positive probability
exactly when a reachable output satisfies it.

gap(simp+grind): these bridges are not in either default set; they are applied by name. -/

example (mx : ProbComp Bool) (x : Bool) : 𝒟[mx] {x} = 0 ↔ x ∉ support mx := by
  fail_if_success (simp; done)  -- gap(simp, 2026-09-26): the bridge is not a simp rule
  fail_if_success grind  -- gap(grind, 2026-09-26): the bridge is not a grind rule
  rw [mem_support_iff_evalDist_singleton_pos, pos_iff_ne_zero, not_not]
example (mx : ProbComp Bool) (x : Bool) : 0 < 𝒟[mx] {x} ↔ x ∈ support mx :=
  (mem_support_iff_evalDist_singleton_pos mx x).symm
example (mx : ProbComp Bool) (p : Bool → Prop) :
    Pr{let x ← mx}[p x] ≠ 0 ↔ {x ∈ support mx | p x}.Nonempty := by
  rw [← pos_iff_ne_zero, prEvent_pos_iff]; rfl
example (mx : ProbComp Bool) (p : Bool → Prop) :
    Pr{let x ← mx}[p x] = 0 ↔ ¬ {x ∈ support mx | p x}.Nonempty := by
  rw [prEvent_eq_zero_iff, Set.not_nonempty_iff_eq_empty, Set.eq_empty_iff_forall_notMem]; simp
example (mx : OptionT ProbComp Bool) (h : (support mx).Nonempty) : Pr{let _ ← mx}[True] ≠ 0 := by
  obtain ⟨x, hx⟩ := h
  exact ((OptionT.prEvent_mk_pos_iff mx.run (fun _ => True)).2
    ⟨x, by simpa [OptionT.support_def] using hx, trivial⟩).ne'

/-! ## 5. Output measures — `𝒟[_]` -/

example (mx : ProbComp Bool) : 𝒟[do let x ← mx; pure x] = 𝒟[mx] := by simp
example (mx : ProbComp Bool) : 𝒟[do let x ← mx; pure x] = 𝒟[mx] := by grind
example (mx : ProbComp Bool) : 𝒟[mx >>= pure] = 𝒟[mx] := by simp
example (mx : ProbComp Bool) : 𝒟[mx >>= pure] = 𝒟[mx] := by grind

/-! ### One-time-pad secrecy
Adding a uniform key makes the ciphertext independent of the message.

gap(simp+grind): translation invariance of a uniform draw is transported along the equivalence
by name. -/

example (msg k : ZMod 2) :
    Pr{let c ← ((msg + ·) <$> ($ᵗ (ZMod 2)) : ProbComp (ZMod 2))}[c = k] =
      Pr{let c ← ($ᵗ (ZMod 2) : ProbComp (ZMod 2))}[c = k] := by
  fail_if_success (simp; done)  -- gap(simp, 2026-09-26): translation invariance
  fail_if_success grind  -- gap(grind, 2026-09-26): translation invariance
  exact SampleableType.prEvent_uniformSample_equiv (Equiv.addLeft msg) (· = k)

/-! ## 6. The shape of `do`
Pure `let :=` steps, nested blocks, pattern-matching binds, branches and long chains, over
`ProbComp` and the failing carrier `OptionT ProbComp`. -/

/-- A pure `let :=` step inside `do`. -/
def coinThenNeg : ProbComp Bool := do
  let x ← $ᵗ Bool
  let y := !x
  pure y

/-- A pattern-matching bind over a nested product draw. -/
def twoThenAnd : ProbComp Bool := do
  let (a, b) ← (do let x ← $ᵗ Bool; let y ← $ᵗ Bool; pure (x, y))
  pure (a && b)

/-- A nested `do` block whose result feeds the outer one. -/
def nestedDraw : ProbComp Bool := do
  let x ← $ᵗ Bool
  let y ← (do let z ← $ᵗ Bool; pure (x && z))
  pure y

/-- An `if`/`then`/`else` branch on a coin. -/
def branchToFin : ProbComp (Fin 2) := do
  let b ← $ᵗ Bool
  if b then pure 0 else pure 1

/-- A twelve-step chain of independent uniform draws. -/
def chain12 : ProbComp Bool := do
  let a ← $ᵗ Bool; let b ← $ᵗ Bool; let c ← $ᵗ Bool; let d ← $ᵗ Bool
  let e ← $ᵗ Bool; let f ← $ᵗ Bool; let g ← $ᵗ Bool; let h ← $ᵗ Bool
  let i ← $ᵗ Bool; let j ← $ᵗ Bool; let k ← $ᵗ Bool; let l ← $ᵗ Bool
  pure (a && b && c && d && e && f && g && h && i && j && k && l)

/-- The same twelve-step chain over the failing carrier `OptionT ProbComp`; it never fails. -/
def chain12Opt : OptionT ProbComp Bool := do
  let a ← $ᵗ Bool; let b ← $ᵗ Bool; let c ← $ᵗ Bool; let d ← $ᵗ Bool
  let e ← $ᵗ Bool; let f ← $ᵗ Bool; let g ← $ᵗ Bool; let h ← $ᵗ Bool
  let i ← $ᵗ Bool; let j ← $ᵗ Bool; let k ← $ᵗ Bool; let l ← $ᵗ Bool
  pure (a && b && c && d && e && f && g && h && i && j && k && l)

/-- A ten-deep tower of redundant `pure` binds that is `$ᵗ Bool`. -/
def coinPadded : ProbComp Bool := do
  let a ← $ᵗ Bool
  let b ← pure a; let c ← pure b; let d ← pure c; let e ← pure d
  let f ← pure e; let g ← pure f; let h ← pure g; let i ← pure h
  let j ← pure i; let k ← pure j
  pure k

/-! ### Losslessness through `do` structure

The lossless-mass law closes an oracle computation's true event without unfolding it; a failing
carrier is unfolded into its lifted draws. -/

example : Pr{let _ ← coinThenNeg}[True] = 1 := by grind
example : Pr{let _ ← coinThenNeg}[True] = 1 := by simp
example : Pr{let _ ← twoThenAnd}[True] = 1 := by simp
example : Pr{let _ ← nestedDraw}[True] = 1 := by simp
example : Pr{let _ ← chain12}[True] = 1 := by simp
example : 𝒟[chain12] Set.univ = 1 := by simp [chain12]
example : Pr{let _ ← chain12Opt}[True] = 1 := by simp [chain12Opt]
example : Pr{let _ ← branchToFin}[True] = 1 := by simp

/-! ### Structural normalization of a deep chain -/

example : 𝒟[coinPadded] = 𝒟[($ᵗ Bool : ProbComp Bool)] := by simp [coinPadded]
example : 𝒟[coinPadded] = 𝒟[($ᵗ Bool : ProbComp Bool)] := by grind [coinPadded]
example : 𝒟[coinPadded] {true} = 𝒟[($ᵗ Bool : ProbComp Bool)] {true} := by simp [coinPadded]
example : support coinPadded = support ($ᵗ Bool : ProbComp Bool) := by simp [coinPadded]
example : (false : Bool) ∈ support chain12 := by simp [chain12]

/-! ### Outcome values of multi-step programs

An event of a derived uniform program such as `coinThenNeg` normalizes to an event of its one
draw, which the uniform event law counts (the counting gap of the header). A long chain stops at a
nest of expectations over its uniform draws, which neither set evaluates: concrete outcome values
of long chains (`𝒟[chain12] {true} = (2 ^ 12)⁻¹`) and the abort mass of a guarded `OptionT`
program are recorded here as `target(simp+grind)` rather than carried as multi-step proofs. -/

example : Pr{let x ← coinThenNeg}[x = true] = 2⁻¹ := by
  fail_if_success (simp [coinThenNeg]; done)  -- gap(simp, 2026-09-30): counting, see header
  fail_if_success grind [coinThenNeg]  -- gap(grind, 2026-09-30): counting, see header
  simp [coinThenNeg, Finset.filter_eq']

/-! ## 7. Cryptography prerequisites
Guessing a uniform secret, collision probability, and masses summing to one. -/

example (guess : Fin 6) : 𝒟[($ᵗ (Fin 6) : ProbComp (Fin 6))] {guess} = 6⁻¹ := by simp
example : Pr{let p ← ($ᵗ (Fin 6 × Fin 6) : ProbComp (Fin 6 × Fin 6))}[p.1 = p.2] = 6 / 36 := by
  fail_if_success (simp; done)  -- gap(simp, 2026-09-26): counting
  fail_if_success grind  -- gap(grind, 2026-09-26): counting
  simp; rfl
example : ∑ k : Fin 6, 𝒟[($ᵗ (Fin 6) : ProbComp (Fin 6))] {k} = 1 := by
  simp [ENNReal.mul_inv_cancel]

/-! ## 8. Abstract carriers
The same facts over an arbitrary `SampleableType` carrier, which carries no measurable space and
need not be finite, so outcomes are `Pr{…}` events.

gap(simp+grind): equiprobability transports along a swap of the sample space, and a product
event factors through `prEvent_bind_bind_and`, both by name. -/

section abstract

variable (α β : Type) [SampleableType α] [SampleableType β]

example (x y : α) :
    Pr{let z ← ($ᵗ α : ProbComp α)}[z = x] = Pr{let z ← ($ᵗ α : ProbComp α)}[z = y] := by
  fail_if_success simp  -- gap(simp, 2026-09-26): abstract equiprobability
  fail_if_success grind  -- gap(grind, 2026-09-26): abstract equiprobability
  classical
  refine Eq.trans ?_ (SampleableType.prEvent_uniformSample_equiv (Equiv.swap x y) (· = y))
  simp [Equiv.swap_apply_eq_iff]

example (z : α × β) :
    Pr{let w ← ((·, ·) <$> ($ᵗ α) <*> ($ᵗ β) : ProbComp (α × β))}[w = z] =
      Pr{let a ← ($ᵗ α : ProbComp α)}[a = z.1] * Pr{let b ← ($ᵗ β : ProbComp β)}[b = z.2] := by
  simp only [expect_norm, Prod.ext_iff]
  exact prEvent_bind_bind_and _ _ _ _

end abstract

/-! ## 9. Swaps and congruence through `prrw` -/

example (mx : ProbComp Bool) (my : ProbComp (Fin 3)) (f : Bool → Fin 3 → ProbComp Bool) :
    Pr{let r ← mx >>= fun a => my >>= fun b => f a b}[r = true] =
      Pr{let r ← my >>= fun b => mx >>= fun a => f a b}[r = true] := by
  prrw

example (mx : ProbComp Bool) (f g : Bool → ProbComp (Fin 3)) (y : Fin 3)
    (h : ∀ b ∈ support mx, 𝒟[f b] {y} = 𝒟[g b] {y}) :
    𝒟[mx >>= f] {y} = 𝒟[mx >>= g] {y} := by
  prrw congr
  exact h _ ‹_›

example (mx : ProbComp Bool) (my : ProbComp (Fin 3)) (f : Bool → Fin 3 → ProbComp Bool) :
    𝒟[mx >>= fun a => my >>= fun b => f a b] = 𝒟[my >>= fun b => mx >>= fun a => f a b] := by
  prrw

/-! ## 10. Events whose continuation destructures its input

The notation turns a destructuring draw into projections of the drawn pair, so the event is a
predicate on the draw and implication between the returned propositions is `prEvent_mono`. A draw
of a destructuring `do` block normalizes to the same event. -/

example (mx : ProbComp (Bool × Bool)) :
    Pr{let (a, b) ← mx}[a = true ∧ b = true] ≤ Pr{let (a, _) ← mx}[a = true] :=
  prEvent_mono mx _ _ fun _ => And.left

example (mx : ProbComp (Bool × Bool)) :
    Pr{let b ← do let (a, b) ← mx; pure (a = true ∧ b = true)}[b] ≤
      Pr{let b ← do let (a, _) ← mx; pure (a = true)}[b] :=
  prEvent_mono mx _ _ fun _ => And.left

end VCVioTest.ProbabilityTactics
