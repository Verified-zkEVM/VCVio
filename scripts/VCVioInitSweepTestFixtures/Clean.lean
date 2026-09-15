/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

import VCVioInitSweepTestFixtures.Clean.Good
import VCVioInitSweepTestFixtures.Clean.Negatives

/-! # Clean fixture root for initsweep

Every declaration reachable from here is one the gate must leave alone. Each submodule
witnesses one clause of the predicate in the negative direction.
-/
