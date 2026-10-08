/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import VCVio.OracleComp.QueryTracking.RandomOracle.ClassIndexedTape
public import VCVio.OracleComp.QueryTracking.RandomOracle.HiddenSeed
public import VCVio.OracleComp.QueryTracking.RandomOracle.Joint

/-!
# The ideal hidden-seed game as one duplicated lazy random oracle

The ideal game `SecretEncoding.idealImpl pub X R` answers public queries from a public cache and
derivation queries from an independent table. Read as one signature, public queries and
derivations form the interface `pub + (X →ₒ R)`, and the pair of caches is one cache on it
under `OracleSpec.QueryCache.addEquiv`.

`SecretEncoding.collapseFwd pub X R` interprets programs over the duplicated forwarded interface
`unifSpec + ((pub + (X →ₒ R)) + (pub + (X →ₒ R)))` in `pub.withDerivations X R`: uniform draws
are forwarded and both copies of a query go to the same public or derivation query. The ideal
game read through it is the duplicated lazy random oracle `AnswerTape.dupRandomOracle` on the
joint cache, with uniform draws forwarded
(`SecretEncoding.map_run_simulateQ_idealImpl_collapseFwd`). The equality is of computations, with
the two caches paired by `addEquiv`; it holds for every program and every initial split state.
-/

public section

open OracleComp OracleSpec

namespace SecretEncoding

variable {ι : Type} (pub : OracleSpec.{0, 0} ι) (X R : Type)

/-- Interpret the duplicated forwarded interface over `pub + (X →ₒ R)` in
`pub.withDerivations X R`: a uniform draw is forwarded, and either copy of a public query or a
derivation becomes that public query or derivation. -/
@[expose] noncomputable def collapseFwd :
    QueryImpl (unifSpec + ((pub + (X →ₒ R)) + (pub + (X →ₒ R))))
      (OracleComp (pub.withDerivations X R))
  | .inl n => liftM ((pub.withDerivations X R).query (.inl (.inl n)))
  | .inr (.inl (.inl t)) | .inr (.inr (.inl t)) =>
      liftM ((pub.withDerivations X R).query (.inl (.inr t)))
  | .inr (.inl (.inr x)) | .inr (.inr (.inr x)) =>
      liftM ((pub.withDerivations X R).query (.inr x))

variable {pub X R} [DecidableEq ι] [DecidableEq X] [SampleableType R]
  [∀ t : pub.Domain, SampleableType (pub.Range t)]

/-- The ideal game, read through `collapseFwd`, is the duplicated lazy random oracle on the joint
cache `pub + (X →ₒ R)` with uniform draws forwarded: the two runs agree once the split state is
paired into the joint cache by `addEquiv`. -/
theorem map_run_simulateQ_idealImpl_collapseFwd {α : Type}
    (oa : OracleComp (unifSpec + ((pub + (X →ₒ R)) + (pub + (X →ₒ R)))) α)
    (st : SplitCache pub X R) :
    Prod.map id (QueryCache.addEquiv pub (X →ₒ R)) <$>
        (simulateQ (idealImpl pub X R) (simulateQ (collapseFwd pub X R) oa)).run st =
      (simulateQ (unifFwdImpl (pub + (X →ₒ R)) +
          AnswerTape.dupRandomOracle (pub + (X →ₒ R))) oa).run
        (QueryCache.addEquiv pub (X →ₒ R) st) := by
  rw [← QueryImpl.simulateQ_compose]
  refine map_run_simulateQ_eq_of_query_map_eq _ _ _ ?_ oa st
  have hpar (t : (pub + (X →ₒ R)).Domain) (st : SplitCache pub X R) :
      ((idealImpl pub X R ∘ₛ collapseFwd pub X R) (.inr (.inl t))).run st =
          ((QueryImpl.parallelStateT pub.randomOracle (X →ₒ R).randomOracle) t).run st ∧
        ((idealImpl pub X R ∘ₛ collapseFwd pub X R) (.inr (.inr t))).run st =
          ((QueryImpl.parallelStateT pub.randomOracle (X →ₒ R).randomOracle) t).run st := by
    rcases t with t | x <;>
      simp [QueryImpl.apply_compose, collapseFwd, idealImpl, QueryImpl.parallelStateT] <;> rfl
  rintro (n | t | t) st
  · simp [QueryImpl.apply_compose, collapseFwd, idealImpl, unifFwdImpl]
  · rw [(hpar t st).1, QueryImpl.add_apply_inr, AnswerTape.dupRandomOracle_apply_inl]
    exact QueryImpl.run_parallelStateT_randomOracle_map_eq t st
  · rw [(hpar t st).2, QueryImpl.add_apply_inr, AnswerTape.dupRandomOracle_apply_inr]
    exact QueryImpl.run_parallelStateT_randomOracle_map_eq t st

end SecretEncoding
