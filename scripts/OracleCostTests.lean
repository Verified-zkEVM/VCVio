/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

import VCVioTest.OracleComp.CostSimulation

/-! # Executable oracle-cost regression checks -/

public section

/-- Execute query-cost refinements on concrete response-dependent programs. -/
def main : IO Unit :=
  VCVioTest.OracleComp.CostSimulation.run
