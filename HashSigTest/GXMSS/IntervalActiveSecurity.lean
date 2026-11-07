/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Interval.Reductions.ActiveSecurity
import all HashSig.GXMSS.Security.Interval.Reductions.ActiveSecurity

/-!
# Active interval probability controls

The inclusive offset controls pin both endpoints of a strict interior interval. The separate
`DirectTrustAudit` checks compiler origins, bodies and allowed transitive axioms, including
private and generated declarations. Ordinary applications separately pin selected theorem types.

Private imports supply the actual implementation kernels used by these controls. Ordinary public
endpoint applications live in `DirectEndpointApplications`.
-/

public section

open GXMSS GXMSS.IntervalMerkle GXMSS.Interval.Unforgeability

#check @activeMatchingMass_le_collision_masses_add_remainder
#check @activeMatchingMass_le_signed_advantages
#check @activeMatchingMass_le_advantages

-- The offset is relative to the first active epoch, including at the upper endpoint.
#check
  let middle : Interval 3 := ⟨3, 4, by decide⟩
  (show (GXMSS.Interval.Unforgeability.activeOffset middle 3 (by decide)).val = 0 ∧
      (GXMSS.Interval.Unforgeability.activeOffset middle 4 (by decide)).val = 1 from by decide)
