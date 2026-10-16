/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Quantum.VC.Unitaries
public import VCVio.Quantum.Oracle.Unitary

/-!
# Emulated oracles for vector commitments

The oracles of the multi-extractability experiments of Chiesa, Di, Hu and Zheng
(ePrint 2025/2166, §7, pp. 50–51), as emulated oracles (`Quantum.EmulatedOracle`):

* `EO = (Init, (O_i)_{i ∈ [k]})` (p. 50): `k` unitary ports on the query register `X × Y`
  (`Quantum.VCOracle`);
* `EO^(Ext) = (Init, ((O_i)_i, U_MultiExtract))` (p. 50): one further port on
  `TpIC × Z`, answered by the purified extractor (`Quantum.VCOracle.withExtract`);
* `EO^(Record)` (p. 51): `EO^(Ext)` with the recording register `R` adjoined in the state
  with every cell at `⊥`, and one further port on `TpIC × Yr`, answered by `Record(U)`
  (`Quantum.VCOracle.withRecord`) or `Record(MultiExtract, U)` (`Quantum.VCOracle.withRecordME`);
* the random-oracle model as an emulated oracle with a trivial private register
  (`Quantum.romVCOracle`, p. 28).

"Polynomial time" of the emulation (p. 50) is not part of the definitions.

## Main definitions

* `Quantum.oIn`, `Quantum.extIn`, `Quantum.recIn`: the port registers.
* `Quantum.VCOracle`, `Quantum.VCOracle.withExtract`, `Quantum.VCOracle.withRecord`,
  `Quantum.VCOracle.withRecordME`, `Quantum.romVCOracle`.
-/

public section

open Matrix
open scoped Kronecker

namespace Quantum

variable (k : ℕ) (X Y : Type) [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

/-! ## Port registers -/

/-- The register of each oracle port: the query register `X × Y` (ePrint 2025/2166, p. 50). -/
abbrev oIn : Fin k → QReg :=
  fun _ ↦ QReg.of (X × Y)

/-- `EO = (Init, (O_i)_{i ∈ [k]})` (ePrint 2025/2166, p. 50): an emulated oracle with `k`
ports on the query register `X × Y`. -/
abbrev VCOracle :=
  EmulatedOracle (Fin k) (oIn k X Y)

/-- The port registers of `EO^(Ext)`: the oracle ports, then the extraction port on `TpIC × Z`
(ePrint 2025/2166, p. 50). -/
abbrev extIn (Cm Z : Type) [Fintype Cm] [DecidableEq Cm] [Fintype Z] [DecidableEq Z] :
    Fin k ⊕ Unit → QReg :=
  Sum.elim (oIn k X Y) fun _ ↦ QReg.of (TpIC k Cm × Z)

/-- The port registers of `EO^(Record)`: the ports of `EO^(Ext)`, then the record port on
`TpIC × Yr` (ePrint 2025/2166, p. 51). -/
abbrev recIn (Cm Z Yr : Type) [Fintype Cm] [DecidableEq Cm] [Fintype Z] [DecidableEq Z]
    [Fintype Yr] [DecidableEq Yr] : (Fin k ⊕ Unit) ⊕ Unit → QReg :=
  Sum.elim (extIn k X Y Cm Z) fun _ ↦ QReg.of (TpIC k Cm × Yr)

variable {k X Y}

namespace VCOracle

variable {Cm Z : Type} [Fintype Cm] [DecidableEq Cm] [Fintype Z] [DecidableEq Z] [AddGroup Z]
  {Dm : Fin k → Type} (E : VCOracle k X Y)

/-! ## Extraction -/

/-- **`EO^(Ext)`** (ePrint 2025/2166, p. 50): the oracle `E` with one further port on
`TpIC × Z`, answered by the purified extractor `U_MultiExtract` on the private register. -/
@[expose]
noncomputable def withExtract (ME : MultiExtractor k Cm Dm E.S) (code : TpDCode k Dm Z) :
    EmulatedOracle (Fin k ⊕ Unit) (extIn k X Y Cm Z) :=
  E.extend (fun _ ↦ extractUnitary ME code) fun _ ↦ extractUnitary_mem_unitaryGroup ME code

variable (ME : MultiExtractor k Cm Dm E.S) (code : TpDCode k Dm Z)

/-- `EO^(Ext)` keeps the private register. -/
@[simp]
theorem withExtract_S : (E.withExtract ME code).S = E.S :=
  rfl

/-- `EO^(Ext)` keeps the initial state. -/
@[simp]
theorem withExtract_init : (E.withExtract ME code).init = E.init :=
  rfl

/-- The oracle ports of `EO^(Ext)` are those of `E`. -/
@[simp]
theorem withExtract_U_inl (i : Fin k) : (E.withExtract ME code).U (.inl i) = E.U i :=
  rfl

/-- The extraction port of `EO^(Ext)` is `U_MultiExtract`. -/
@[simp]
theorem withExtract_U_inr (u : Unit) :
    (E.withExtract ME code).U (.inr u) = extractUnitary ME code :=
  rfl

/-! ## Recording -/

variable {Yr Cell : Type} [Fintype Yr] [DecidableEq Yr] [Fintype Cell] [DecidableEq Cell]
  [∀ i, Fintype (Dm i)] [∀ i, DecidableEq (Dm i)]

/-- `EO^(Ext)` with the recording register `R` adjoined in the state with every cell at `bot`
(the step from `Init` to `Init′` of ePrint 2025/2166, p. 51). -/
@[expose, reducible]
noncomputable def withRecReg (bot : Cell) : EmulatedOracle (Fin k ⊕ Unit) (extIn k X Y Cm Z) :=
  (E.withExtract ME code).addRegister (QReg.of (RecReg k Cm Dm Cell))
    (SubState.basis (RecReg.const bot))

/-- **`EO^(Record)` in the world `Record(U)`** (ePrint 2025/2166, p. 51): `EO^(Ext)` with
the recording register adjoined, every cell at `bot`, and one further port on `TpIC × Yr`
answered by `Record(U)`. -/
@[expose]
noncomputable def withRecord (bot : Cell) (U : Matrix (Yr × Cell) (Yr × Cell) ℂ)
    (hU : U ∈ unitaryGroup (Yr × Cell) ℂ) :
    EmulatedOracle ((Fin k ⊕ Unit) ⊕ Unit) (recIn k X Y Cm Z Yr) :=
  (E.withRecReg ME code bot).extend (fun _ ↦ recordUnitary U)
    fun _ ↦ recordUnitary_mem_unitaryGroup hU

/-- **`EO^(Record)` in the world `Record(MultiExtract, U)`** (ePrint 2025/2166, p. 51): as
`Quantum.VCOracle.withRecord`, with the record port answered by `Record(MultiExtract, U)`. -/
@[expose]
noncomputable def withRecordME (bot : Cell) (U : Matrix (Yr × Cell) (Yr × Cell) ℂ)
    (hU : U ∈ unitaryGroup (Yr × Cell) ℂ) :
    EmulatedOracle ((Fin k ⊕ Unit) ⊕ Unit) (recIn k X Y Cm Z Yr) :=
  (E.withRecReg ME code bot).extend (fun _ ↦ recordMEUnitary ME U)
    fun _ ↦ recordMEUnitary_mem_unitaryGroup ME hU

variable (bot : Cell) (U : Matrix (Yr × Cell) (Yr × Cell) ℂ) (hU : U ∈ unitaryGroup (Yr × Cell) ℂ)

/-- The two record worlds share their ports other than the record port. -/
theorem withRecord_U_inl (i : Fin k ⊕ Unit) :
    (E.withRecord ME code bot U hU).U (.inl i) = (E.withRecordME ME code bot U hU).U (.inl i) :=
  rfl

/-- The record port of `Record(U)`. -/
@[simp]
theorem withRecord_U_inr (u : Unit) :
    (E.withRecord ME code bot U hU).U (.inr u) = recordUnitary U :=
  rfl

/-- The record port of `Record(MultiExtract, U)`. -/
@[simp]
theorem withRecordME_U_inr (u : Unit) :
    (E.withRecordME ME code bot U hU).U (.inr u) = recordMEUnitary ME U :=
  rfl

/-- The two record worlds start in the same state. -/
theorem withRecord_init :
    (E.withRecord ME code bot U hU).init = (E.withRecordME ME code bot U hU).init :=
  rfl

end VCOracle

/-! ## The random-oracle model -/

/-- **The random-oracle model as an emulated oracle** (ePrint 2025/2166, p. 28): a trivial
private register, and the port `i` answered by the oracle unitary `|x, y⟩ ↦ |x, y + H i x⟩`. -/
@[expose]
noncomputable def romVCOracle (k : ℕ) (X Y : Type) [Fintype X] [DecidableEq X] [Fintype Y]
    [DecidableEq Y] [AddCommGroup Y] (H : Fin k → X → Y) : VCOracle k X Y where
  S := QReg.of Unit
  init := SubState.basis ()
  U i := oracleUnitary (H i) ⊗ₖ (1 : Matrix Unit Unit ℂ)
  unitary i := kronecker_mem_unitary (oracleUnitary_mem_unitaryGroup (H i)) (one_mem _)

end Quantum
