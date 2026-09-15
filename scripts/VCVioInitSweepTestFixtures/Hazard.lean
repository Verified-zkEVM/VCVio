/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

import VCVioInitSweepTestFixtures.Hazard.Initialize
import VCVioInitSweepTestFixtures.Hazard.Noncomputable
import VCVioInitSweepTestFixtures.Hazard.Plain

/-! # Hazard fixture root for initsweep

The two spellings a source-level rule cannot tell apart, plus the `initialize` route that
has no parameterless value of its own. The first two are flagged on the same constant —
the compiled auxiliary, not the instance — and the third on the declaration whose
registered initialiser body carries the enumeration.
-/
