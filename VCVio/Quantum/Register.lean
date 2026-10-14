/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import Mathlib.Data.Fintype.Basic

/-!
# Quantum registers

A register of a quantum program is a finite basis type with decidable equality: the operators on
the register are the complex matrices indexed by it. `Quantum.QReg` bundles such a type with its
instances, so that registers can be the indices of a type family. Quantum programs
(`Quantum.QuantumComp`) are indexed by the register they start on, and each leaf of a program
sits on its own final register.

## Main definitions

* `Quantum.QReg`: a finite type with decidable equality, coerced to its carrier.
* `Quantum.QReg.of A`: the register with basis `A`.
-/

public section

namespace Quantum

/-- A quantum register: a finite basis type with decidable equality. -/
structure QReg : Type 1 where
  /-- The basis of the register. -/
  carrier : Type
  /-- The basis is finite. -/
  [fintype : Fintype carrier]
  /-- The basis has decidable equality. -/
  [decEq : DecidableEq carrier]

namespace QReg

instance : CoeSort QReg Type := ⟨QReg.carrier⟩

attribute [instance] QReg.fintype QReg.decEq

/-- The register with basis `A`. -/
abbrev of (A : Type) [Fintype A] [DecidableEq A] : QReg := ⟨A⟩

end QReg

end Quantum
