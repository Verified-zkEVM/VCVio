/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Statement.Security
public import HashSig.SLHDSA.SHAKE128s.Proof.WorkFinal

/-!
# StrongUnforgeability
-/

@[expose] public section

namespace SlhDsaSecurity

open Security

/-- **SLH-DSA-SHAKE-128s has 127 bits of strong unforgeability**, counting the adversary's
signing requests, its hash calls and the verification of its forgery. -/
theorem slhDsa_sufCma_127 : HasSecurityBits adversaryWork 127 :=
  WorkFinal.hasSecurityBits_work

/-- info: 'SlhDsaSecurity.slhDsa_sufCma_127' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms slhDsa_sufCma_127

end SlhDsaSecurity
