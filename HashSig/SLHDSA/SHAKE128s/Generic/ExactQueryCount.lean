/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import VCVio.OracleComp.OracleComp

/-!
# Exact query counts

`ExactQueryCount computation count`: on every path, `computation` makes exactly `count` oracle
queries. It is closed under `bind` and `map`.
-/

public section

open OracleComp OracleSpec

namespace SLHDSA.SHAKE128s.Generic

variable {ι : Type} {spec : OracleSpec ι} {α β : Type}

/-- On every path, the computation makes exactly `count` oracle queries. -/
inductive ExactQueryCount :
    OracleComp spec α → Nat → Prop where
  /-- A returned value makes no queries. -/
  | pure (value : α) : ExactQueryCount (pure value) 0
  /-- One query followed, on every answer, by exactly `count` more makes `count + 1`. -/
  | query (input : spec.Domain) (next : spec.Range input → OracleComp spec α)
      (count : Nat) (hnext : ∀ output, ExactQueryCount (next output) count) :
      ExactQueryCount (liftM (spec.query input) >>= next) (count + 1)

namespace ExactQueryCount

/-- Running a computation with exactly `count` queries, then a continuation with exactly
`nextCount` queries on every value, makes exactly `count + nextCount` queries. -/
theorem bind {computation : OracleComp spec α} {count : Nat}
    (hcomputation : ExactQueryCount computation count)
    (next : α → OracleComp spec β) (nextCount : Nat)
    (hnext : ∀ value, ExactQueryCount (next value) nextCount) :
    ExactQueryCount (computation >>= next) (count + nextCount) := by
  induction hcomputation with
  | pure value => simpa using hnext value
  | query input rest restCount hrest ih =>
      rw [bind_assoc]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ExactQueryCount.query input (fun output => rest output >>= next)
          (restCount + nextCount) ih

/-- Mapping a function over the output does not change the number of queries. -/
theorem map {computation : OracleComp spec α} {count : Nat}
    (hcomputation : ExactQueryCount computation count) (f : α → β) :
    ExactQueryCount (f <$> computation) count := by
  convert hcomputation.bind
    (fun value => (Pure.pure (f value) : OracleComp spec β)) 0
    (fun value => ExactQueryCount.pure (f value)) using 1
  simp [map_eq_bind_pure_comp]

end ExactQueryCount

end SLHDSA.SHAKE128s.Generic
