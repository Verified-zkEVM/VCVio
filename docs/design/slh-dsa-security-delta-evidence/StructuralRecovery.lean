/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.Security.Wire
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Structural security bounds at deterministic SHAKE-128s

The exact byte-model envelope retains its weak-seed contribution. Its zero-query value
provides a comparison with the work selected by a universal verifier cap.
-/

public section

open SignatureAlg
open scoped ENNReal

namespace SLHDSA.SecurityDelta

/-- The validated deterministic SHAKE-128s parameter bundle. -/
abbrev vp : ValidatedParams := FipsParameterSet.SLHDSA_SHAKE_128s.validatedParams

/-- The complete averaged deterministic byte-model bound. -/
@[expose] noncomputable def envelope (qh qs : Nat) : ℝ≥0∞ :=
  Security.byteBound vp qh qs + Security.honestAdrsCount vp / 2 ^ 256 *
    Security.weakSeedFactor vp (Security.everySeedBound vp qh qs)

/-- The structural byte-wire theorem at its unchanged query caps. -/
theorem structural_bound (ctx : Security.PureContext)
    (adv : StrongUnforgeableAdversary
      (Security.wireShakeScheme vp ctx (fun pk => pure pk.pkSeed)
        ($ᵗ (Security.shakeCore vp).PkSeed)))
    {qh qs : Nat} (hadv : adv.RomQueryBound qh qs) :
    strongUnforgeableAdvantage (Security.shakeRuntime vp) adv ≤ envelope qh qs :=
  Security.wireStrongAdvantage_le_securityBound_validatedParams .SLHDSA_SHAKE_128s ctx adv hadv

/-- The SHAKE-128s digest width is sixteen bytes. -/
theorem n_eq : vp.params.n = 16 := by decide

/-- The existing universal internal-verifier cap at SHAKE-128s. -/
theorem verifier_eq : GeneralScheme.verifyInternalQueryBound vp.params = 3929 := by decide

/-- With no adversary or signing queries the byte term still pays verifier work. -/
theorem byte_zero : Security.byteBound vp 0 0 = (7859 : ℝ≥0∞) / 2 ^ 128 := by
  have hk : 0 < vp.params.k := by decide
  simp [Security.byteBound, Security.securityBound,
    KeyedHash.Covering.weightedTargetCoverBound_qw_zero,
    KeyedHash.Covering.targetCoverBound_zero (h := vp.params.h) (a := vp.params.a)
      (k := vp.params.k) hk, n_eq, verifier_eq, div_eq_mul_inv]
  ring

/-- The complete structural envelope at zero direct and signing queries. -/
theorem envelope_zero : envelope 0 0 = (7859 : ℝ≥0∞) / 2 ^ 128 +
    Security.honestAdrsCount vp / 2 ^ 256 := by
  rw [envelope, byte_zero, Security.weakSeedFactor_of_ne (by decide), mul_one]

/-- The structural envelope exceeds the linear work expression at the universal verifier cap. -/
theorem zero_caps_obstruction : (3929 : ℝ≥0∞) / 2 ^ 127 < envelope 0 0 := by
  have strict : (3929 : ℝ≥0∞) / 2 ^ 127 < (7859 : ℝ≥0∞) / 2 ^ 128 := by
    apply (ENNReal.toReal_lt_toReal (by finiteness) (by finiteness)).mp
    norm_num
  exact strict.trans_le (by rw [← byte_zero]; exact le_self_add)

end SLHDSA.SecurityDelta

#print axioms SLHDSA.SecurityDelta.structural_bound
#print axioms SLHDSA.SecurityDelta.byte_zero
#print axioms SLHDSA.SecurityDelta.envelope_zero
#print axioms SLHDSA.SecurityDelta.zero_caps_obstruction
