/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.PRFDerived.Unforgeability

/-!
# PRF-derived GXMSS security import audit

The separate `TrustAudit` enforces theorem kind and compiler origin for the five public
security results. That audit also checks transitive axioms of every declaration imported from the
security module, including private helpers and generated auxiliaries. The audit checks trust
and origin; the theorem statements retain their explicit sampling and generic-security premises.
-/

public section

open GXMSS.PRFDerived.Unforgeability

#check @randgenPRFReduction_real_strong
#check @randgenPRFReduction_functionQuery_bound
#check @ideal_adaptive_strong_correspondence
#check @adaptive_strong_additive_bound
#check @strong_unforgeability_reduction_bound
