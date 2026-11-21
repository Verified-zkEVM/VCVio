/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VCVio Contributors
-/

module

public import VCVio.OracleComp.QueryTracking.RandomOracle.AcceptedScan.Compensation

/-!
# A partner outside the finder's address family

The finder reads address false.
A probe of true can give that stored word its first partner.
-/

public section

open OracleSpec OracleComp AcceptedScan randomOracle.Partners
open scoped ENNReal

namespace VCVioTest.RandomOraclePartnerCompensation

/-- The accepted bit decodes to the unique digest. -/
@[expose] def decode (v : Bool) : Option Unit := if v then some () else none

open Classical in
/-- An existing true word is the first and only selection. -/
private theorem one_row (c : QueryCache (Bool →ₒ Bool)) (present : c false = some true) :
    partneredMass (fun _ => ()) decode {true} (fun _ : Unit => false) [()] c =
      if Partner (fun _ => ()) decode c false then 1 else 0 := by
  classical
  simp only [partneredMass, scan_cons, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
    QueryImpl.withCaching_run_some _ present, pure_bind, Finset.mem_singleton, ↓reduceIte,
    simulateQ_pure, StateT.run_pure, prEvent_norm]
  simp

/-- The prior selected mass moves from zero to one on a matching reply at the other address. -/
theorem different_address :
    let c : QueryCache (Bool →ₒ Bool) := QueryCache.ofFn fun b => if b then none else some true
    let mass := partneredMass (fun _ => ()) decode {true} (fun _ : Unit => false) [()]
    mass c = 0 ∧ mass (c.cacheQuery true true) = 1 ∧ mass (c.cacheQuery true false) = 0 := by
  classical
  intro c mass
  have low : c false = some true := rfl
  have other (v : Bool) : (c.cacheQuery true v) false = some true :=
    (QueryCache.cacheQuery_of_ne c v (by decide : false ≠ true)).trans low
  have unique (b : Bool) (ne : b ≠ false) : b = true := by cases b <;> simp_all
  have bad : ¬Partner (fun _ => ()) decode c false := by
    rintro ⟨_, _, _, _, b, ne, _, w, hw, _⟩
    rw [unique b ne] at hw
    cases hw
  have hit : Partner (fun _ => ()) decode (c.cacheQuery true true) false :=
    ⟨true, other _, (), rfl, true, by decide, rfl, true, QueryCache.cacheQuery_self .., rfl⟩
  have miss : ¬Partner (fun _ => ()) decode (c.cacheQuery true false) false := by
    rintro ⟨_, _, _, _, b, ne, _, w, hw, hd⟩
    rw [unique b ne, QueryCache.cacheQuery_self, Option.some_inj] at hw
    subst w
    cases hd
  simp only [mass, one_row _ low, one_row _ (other true), one_row _ (other false),
    bad, hit, miss, ite_false, ite_true,
    and_self]

end VCVioTest.RandomOraclePartnerCompensation
