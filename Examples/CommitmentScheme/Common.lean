/-
Copyright (c) 2026 James Waters. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James Waters
-/

module
public import VCVio.OracleComp.EvalDist
public import VCVio.OracleComp.Coercions.Add.Basic
public import VCVio.OracleComp.SimSemantics.Append
public import VCVio.OracleComp.QueryTracking.Unpredictability
public import VCVio.EvalDist.TVDist
public import VCVio.ProgramLogic.Notation
public import VCVio.ProgramLogic.Relational.SimulateQ

/-!
# Random-oracle commitment scheme — shared definitions

Shared oracle and scheme definitions plus the basic single-fresh-query
unpredictability lemma used throughout the binding, extractability, and
hiding proofs in `Examples/CommitmentScheme/`.

The scheme: commit to a message `m : M` by sampling a uniform salt
`s : S` and outputting `(H(m, s), s)`, where `H : (M × S) → C` is the
random oracle.

* `CMOracle M S C` — the random-oracle spec `H : (M × S) → C`.
* `CMCommit m s` — the commit algorithm (queries `H` at `(m, s)`).
* `CMCheck c m s` — the verification algorithm (queries `H` at `(m, s)`,
  compares to the supplied commitment).
* `prEvent_from_fresh_query_le_inv` — basic `1/|C|` unpredictability
  bound for a single fresh oracle query.

When run under `cachingOracle` from an empty cache, all queries by both
adversary and verifier share the same random function — this is how we
model the *shared* random oracle.

`prEvent_from_fresh_query_le_inv` is the atomic building block that all
three security proofs reduce to: a single fresh oracle answer is
distributionally `Uniform C`, so it hits any fixed target with probability
exactly `1/|C|`. Composed with the birthday bound on cache collisions and
identical-until-bad TV-distance bounds, this fact powers the binding,
extractability, and hiding theorems.
-/

@[expose] public section

open OracleSpec OracleComp ENNReal

/-! ## Oracle and scheme algorithms -/

/-- Oracle spec for the random-oracle commitment scheme:
the random oracle has signature `H : (M × S) → C`. -/
abbrev CMOracle (M : Type) (S : Type) (C : Type) : OracleSpec (M × S) := fun _ => C

/-- The commitment oracle samples uniformly in its chosen finite response space. -/
noncomputable instance {M S C : Type} [Fintype C] [Inhabited C]
    [MeasurableSpace C] [MeasurableSingletonClass C] :
    OracleSpec.IsUniformMeasureSpec (CMOracle M S C) :=
  OracleSpec.IsUniformMeasureSpec.ofFiniteNonempty _

variable {M S C : Type} [DecidableEq M] [DecidableEq S] [Fintype C] [Inhabited C]

noncomputable instance : IsUniformSpec (CMOracle M S C) :=
  IsUniformSpec.ofFintypeInhabited _

/-- Commit to message `m` with salt `s` by querying the random oracle at `(m, s)`. -/
def CMCommit (m : M) (s : S) : OracleComp (CMOracle M S C) C :=
  (CMOracle M S C).query (m, s)

/-- Check commitment `c` against opening `(m, s)`: query the oracle at `(m, s)` and
compare to `c`. Under a shared `cachingOracle` this returns the same value the
honest commit phase wrote into the cache. -/
def CMCheck [DecidableEq C] (c : C) (m : M) (s : S) : OracleComp (CMOracle M S C) Bool := do
  let c' ← (CMOracle M S C).query (m, s)
  return (c == c')

/-! ## Single-fresh-query unpredictability -/

/-- **Single fresh-query unpredictability bound (`1/|C|`).**

If `t` is *fresh* in the cache `cache₀` and the only way for the
continuation `cont` to win is for the fresh query at `t` to return a fixed
target value, then the win probability is at most `1/|C|`. The atomic
fact: a fresh random-oracle answer is uniform on `C`, so it equals any
specific target with probability exactly `1/|C|`. -/
lemma prEvent_from_fresh_query_le_inv [MeasurableSpace C] [MeasurableSingletonClass C]
    (t : (CMOracle M S C).Domain)
    (target : C)
    (cache₀ : QueryCache (CMOracle M S C))
    (hfresh : cache₀ t = none)
    (cont : C → OracleComp (CMOracle M S C) Bool)
    (hzero : ∀ u, u ≠ target →
      Pr{let z ← (simulateQ cachingOracle (cont u)).run
             (cache₀.cacheQuery t u)}[z.1 = true] = 0) :
    Pr{let z ← (simulateQ (CMOracle M S C).cachingOracle do
        let u ← (CMOracle M S C).query t
        cont u).run cache₀}[z.1 = true] ≤
      (Fintype.card C : ℝ≥0∞)⁻¹ := by
  classical
  have hrun :
      (simulateQ (CMOracle M S C).cachingOracle do
        let u ← (CMOracle M S C).query t
        cont u).run cache₀ =
      (do
        let u ← (CMOracle M S C).query t
        (simulateQ cachingOracle (cont u)).run (cache₀.cacheQuery t u)) := by
    simp only [simulateQ_query_bind, OracleQuery.input_query, StateT.run_bind]
    have hstep :
        (liftM ((CMOracle M S C).cachingOracle t) :
          StateT (QueryCache (CMOracle M S C))
            (OracleComp (CMOracle M S C)) _).run cache₀ =
        (do
          let u ← (CMOracle M S C).query t
          pure (u, cache₀.cacheQuery t u)) := by
      simp only [cachingOracle.apply_eq, liftM, MonadLiftT.monadLift, MonadLift.monadLift,
        StateT.run_bind, StateT.run_get, monad_norm, hfresh]
      change (StateT.lift
        (PFunctor.FreeM.lift (P := (CMOracle M S C).toPFunctor) t) cache₀ >>= _) = _
      simp only [StateT.lift, monad_norm,
        modifyGet, MonadState.modifyGet, MonadStateOf.modifyGet,
        StateT.modifyGet, StateT.run]
      rfl
    rw [hstep, bind_assoc]
    simp [OracleQuery.cont_query]
  rw [hrun]
  refine (prEvent_bind_le_prEvent_of_forall_eq_zero _ _ (fun u => u = target) _
    fun u hu => hzero u hu).trans (le_of_eq ?_)
  rw [prEvent_liftM_query_eq_card_div, Finset.filter_eq' Finset.univ target]
  simp
