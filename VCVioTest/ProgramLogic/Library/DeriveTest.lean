/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.ProgramLogic.Library.Derive
public import VCVio.CryptoFoundations.GPVHashAndSign.CombinedHandler
public import VCVio.CryptoFoundations.FiatShamir.Sigma.Fork
public import VCVio.CryptoFoundations.PRF
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTTCR
public import VCVio.CryptoFoundations.HardnessAssumptions.KeyedHash.ITSR
public import Examples.CommitmentScheme.Hiding.Defs
public import Examples.PRFTagReader.PRFReductions.IdealHandlers

/-!
# Tests for `derive_handler_specs`

A toy handler defined by pattern matching on an inductive query type and a sum of handlers
check the branch enumeration and the names; handlers of the GPV, Fiat-Shamir, PRF,
PRF-tag-reader, commitment-hiding and hardness-assumption developments check that the derived
equations close their hand-written one-step run equations, restated by `type_of%`, in one line.
-/

public section

open OracleSpec OracleComp

namespace DeriveTest

/-! ## Constructor and sum branches -/

/-- Queries of a toy counter: read it or overwrite it. -/
inductive CounterQuery
  | read
  | write (n : ℕ)

/-- A read answers a natural number and a write answers nothing. -/
abbrev counterSpec : OracleSpec CounterQuery
  | .read => ℕ
  | .write _ => Unit

/-- A handler defined by pattern matching on the query. -/
@[expose] def counterImpl : QueryImpl counterSpec (StateT ℕ ProbComp)
  | .read => get
  | .write n => set n

/-- Uniform queries forwarded to the base monad. -/
@[expose] def coinImpl : QueryImpl unifSpec (StateT ℕ ProbComp) :=
  fun n => monadLift (unifSpec.query n : ProbComp _)

/-- A sum of two named handlers. -/
@[expose] def counterWithCoins : QueryImpl (unifSpec + counterSpec) (StateT ℕ ProbComp) :=
  coinImpl + counterImpl

/--
info: 4 lemmas on 2/2 branches:
  theorem DeriveTest.counterImpl.apply_read : counterImpl CounterQuery.read = get
  theorem DeriveTest.counterImpl.run_read : ∀ (s : ℕ), (counterImpl CounterQuery.read).run s = pure (s, s)
  theorem DeriveTest.counterImpl.apply_write : ∀ (n : ℕ), counterImpl (CounterQuery.write n) = set n
  theorem DeriveTest.counterImpl.run_write : ∀ (n s : ℕ),
    (counterImpl (CounterQuery.write n)).run s = pure (PUnit.unit, n)
-/
#guard_msgs in
derive_handler_specs? counterImpl

derive_handler_specs counterImpl
derive_handler_specs coinImpl
derive_handler_specs counterWithCoins

example (s : ℕ) : (counterImpl .read).run s = pure (s, s) := counterImpl.run_read s

/-- The sum dispatches to its summands, whose own run equations then apply. -/
example (n s : ℕ) : (counterWithCoins (.inr (.write n))).run s = pure ((), n) := by
  simp [counterWithCoins.run_inr]

example : counterWithCoins (.inr .read) = counterImpl .read := counterWithCoins.apply_inr _

/-- The `run_` lemmas are simp lemmas, so a simulation of the sum handler runs to a value. -/
example : (simulateQ counterWithCoins (do
      let _ ← liftM ((unifSpec + counterSpec).query (.inr (.write 3)))
      liftM ((unifSpec + counterSpec).query (.inr .read))
      : OracleComp (unifSpec + counterSpec) ℕ)).run' 0 = pure 3 := by
  simp [simulateQ_nf]

/-! ## GPV hash-and-sign: three summands, a cache lookup in the state -/

derive_handler_specs GPVHashAndSign.reductionImpl

/-- The hand-written random-oracle step (19 lines with its proof) is the derived equation. -/
example : type_of% @GPVHashAndSign.reductionImpl_run_inl_inr := by
  intros; simp [GPVHashAndSign.reductionImpl.run_inl_inr]

example : type_of% @GPVHashAndSign.reductionImpl_run_inr := by
  intros; simp [GPVHashAndSign.reductionImpl.run_inr]

/-- A cache hit is a one-step goal closed by the run equation and the hit. -/
example {PK SK Domain Range : Type} [DecidableEq Range]
    (psf : PreimageSampleableFunction PK SK Domain Range) (M Salt : Type) [DecidableEq M]
    [DecidableEq Salt] [SampleableType Salt] (domainSample : PK → ProbComp Domain) (pk : PK)
    (q : Salt × M) (s : (Salt × M →ₒ Range).QueryCache × ((Salt × M) → Option Domain)) (v : Range)
    (hq : s.1 q = some v) :
    (GPVHashAndSign.reductionImpl psf M Salt domainSample pk (.inl (.inr q))).run s =
      pure (v, s) := by
  simp [hq]

/-! ## Fiat-Shamir forking: a destructuring `get` and a cache `match` -/

derive_handler_specs FiatShamir.Fork.roImpl

example : type_of% @FiatShamir.Fork.roImpl_run_none := by
  intros; simp [FiatShamir.Fork.roImpl.run, *]

example : type_of% @FiatShamir.Fork.roImpl_run_some := by
  intros; simp [FiatShamir.Fork.roImpl.run, *]

/-! ## PRF scheme: a handler into `ProbComp`, whose `apply_` lemmas are simp lemmas -/

derive_handler_specs PRFScheme.prfRealQueryImpl

example {K D R : Type} (prf : PRFScheme K D R) (k : K) (d : D) :
    prf.prfRealQueryImpl k (.inr d) = pure (prf.eval k d) := by
  simp

/-! ## PRF tag reader: a dependent `if` on the session counter -/

derive_handler_specs PRFTagReader.unlinkToSinglePRFTagImpl

example : type_of% @PRFTagReader.unlinkToSinglePRFTagImpl_run_of_lt := by
  intros; simp [PRFTagReader.unlinkToSinglePRFTagImpl.run, *]

example : type_of% @PRFTagReader.unlinkToSinglePRFTagImpl_run_of_not_lt := by
  intros; simp [PRFTagReader.unlinkToSinglePRFTagImpl.run, *]

/-! ## Commitment hiding: a salt counter beside the cache -/

derive_handler_specs hidingImpl₁

example {M S C : Type} [DecidableEq M] [DecidableEq S] (s : S) (ms : M × S)
    (cache : QueryCache (CMOracle M S C)) (cnt : ℕ) (u : C) (hcache : cache ms = some u) :
    (hidingImpl₁ s ms).run (cache, cnt) = pure (u, (cache, cnt)) := by
  simp [hidingImpl₁.run, hcache]

/-! ## Hardness assumptions: an `if` on the challenge budget, and a key-recording oracle -/

derive_handler_specs TweakableHash.SM_DT_TCR_challengeOracle
derive_handler_specs KeyedHash.ITSRTargetOracle

example : type_of% @TweakableHash.SM_DT_TCR_challengeOracle_run_of_full := by
  intros; simp [TweakableHash.SM_DT_TCR_challengeOracle.run, *]

/-- A fresh query below the budget: the side conditions are passed to simp. -/
example {ι PkSeed Tweak M Y : Type} [DecidableEq Tweak]
    (prob : TweakableHash.SM_DT_TCR_Problem ι PkSeed Tweak M Y) (pk : PkSeed) (t : Tweak) (m : M)
    (qsChal : List (Tweak × M)) (twsColl : List Tweak) (hlen : qsChal.length < prob.numTargets)
    (hfresh : TweakableHash.TweakFresh Prod.fst qsChal twsColl t) :
    (TweakableHash.SM_DT_TCR_challengeOracle prob pk (t, m)).run (qsChal, twsColl) =
      pure (some (prob.th.eval pk t m), (qsChal ++ [(t, m)], twsColl)) := by
  simp [TweakableHash.SM_DT_TCR_challengeOracle.run, Nat.not_le.mpr hlen, hfresh]

/-- The `run_` lemmas are simp lemmas: `simp` alone closes the hand-written equation. -/
example : type_of% @KeyedHash.ITSRTargetOracle_run := by
  intros; simp

end DeriveTest
