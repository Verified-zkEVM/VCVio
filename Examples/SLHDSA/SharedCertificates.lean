/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.SHAKE128s.Bridge.SharedExperiment.Certificates

/-!
# Choosing an eligible shared-work certificate

Use the matching zero theorem below 569 actual joint selected calls. Otherwise the 127-bit
certificate requires a positive cap and the original almost-sure signing lifetime. These are
the deterministic SHAKE-128s empty-cache shared-ROM games, with per-request message/context,
oversized rejection and independent uniform seeds. Their selected-work `q` is distinct from
the Profile `(qh, qs)` metric; these clients assert no minimum between the two metrics.
-/

public section

open OracleComp OracleSpec SignatureAlg
open SLHDSA.SHAKE128s
open SLHDSA.SHAKE128s.Bridge.SharedExperiment
open scoped ENNReal

namespace SLHDSA.SHAKE128s.Examples.SharedCertificates

/-- The model's eligible small-work certificate needs neither positivity nor lifetime. -/
theorem zero_model (adv : Game.Adversary HashOutput PublicKey) (q : Nat) (hq : q < 569)
    (hbound : (observedGame Bridge.model).HasQueryBound () Game.adversaryWork adv q) :
    (observedGame Bridge.model).advantage () adv = 0 :=
  Bridge.SharedExperiment.advantage_eq_zero_model adv q hq hbound

/-- The full30-byte FIPS game's eligible small-work certificate has the same zero conclusion. -/
theorem zero_fips (adv : Game.Adversary FIPS205.Answer (SLHDSA.PublicKeyCore FIPS205.core))
    (q : Nat) (hq : q < 569)
    (hbound : (observedGame FIPS205.scheme).HasQueryBound () Game.adversaryWork adv q) :
    (observedGame FIPS205.scheme).advantage () adv = 0 :=
  Bridge.SharedExperiment.advantage_eq_zero_fips adv q hq hbound

/-- Positive shared work retains q/2^127 under the original signing lifetime. -/
theorem positive_fips (q : Nat) (hq : 1 ≤ q)
    (adv : Game.Adversary FIPS205.Answer (SLHDSA.PublicKeyCore FIPS205.core))
    (hlimit :
      Pr{let result ← (observedGame FIPS205.scheme).experiment () adv}[result.2 .sign ≤ 2 ^ 64] = 1)
    (hbound : (observedGame FIPS205.scheme).HasQueryBound () Game.adversaryWork adv q) :
    (observedGame FIPS205.scheme).advantage () adv ≤ q / ((2 ^ 127 : Nat) : ℝ≥0∞) :=
  Bridge.SharedExperiment.advantage_le_127 q hq adv hlimit hbound

end SLHDSA.SHAKE128s.Examples.SharedCertificates
