/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

import VCVioInitSweepTestFixtures.Hazard.Decide
import VCVioInitSweepTestFixtures.Hazard.Initialize
import VCVioInitSweepTestFixtures.Hazard.Named
import VCVioInitSweepTestFixtures.Hazard.Noncomputable
import VCVioInitSweepTestFixtures.Hazard.Opaque
import VCVioInitSweepTestFixtures.Hazard.Plain

/-! # Hazard fixture root for initsweep

The two spellings a source-level rule cannot tell apart, the respelling a *name* test
cannot tell apart from a fix, the `initialize` route that has no parameterless value of its
own, and the route that mentions no enumeration at all. `Plain` and `Noncomputable` are
flagged on the same constant — the compiled auxiliary, not the instance; `Named` reaches the
same enumeration through `Pi.instFintype`, which no entry-point name matches; `Initialize` is
flagged on the declaration whose registered initialiser body carries the enumeration;
`Decide` writes no instance at all and enumerates through the `Decidable` instance; and
`Opaque` hides its value from the kernel's view and not from the backend.
-/
