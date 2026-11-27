/-
Copyright (c) 2026 Quang Dao, Tom Wambsgans, Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Tom Wambsgans, Alexander Hicks
-/

module
public import Init.Control.Basic

/-!
# Internal SLH-DSA component sequencing

The supplied-randomizer boundary composes the actual message digest, FORS and hypertree
components. Sampling, message framing, signature parsing and oracle interpretation remain
with their existing owners. The callbacks preserve the complete order of component effects.
-/

public section

universe u v

namespace SLHDSA.Scheme.Program

variable {Y Digest Parts ForsSig HtSig Signature Keys Result : Type u}
variable {m : Type u → Type v} [Monad m]

/-- Assemble supplied-seed key material after the existing top-root component. -/
@[expose] def keygen (root : m Y) (pack : Y → Keys) : m Keys := do
  let value ← root
  return pack value

/-- Sign at a supplied randomizer, recovering the FORS signature before hypertree signing. -/
@[expose] def sign (messageDigest : m Digest) (split : Digest → Parts)
    (forsSign : Parts → m ForsSig) (forsRecover : Parts → ForsSig → m Y)
    (hypertreeSign : Parts → Y → m HtSig) (pack : ForsSig → HtSig → Signature) : m Signature := do
  let digest ← messageDigest
  let parts := split digest
  let forsSignature ← forsSign parts
  let root ← forsRecover parts forsSignature
  let hypertreeSignature ← hypertreeSign parts root
  return pack forsSignature hypertreeSignature

/-- Recover both supplied signature components before the pure comparison with the claimed root. -/
@[expose] def verify (messageDigest : m Digest) (split : Digest → Parts)
    (forsRecover : Parts → m Y) (hypertreeRecover : Parts → Y → m Y)
    (accept : Y → Result) : m Result := do
  let digest ← messageDigest
  let parts := split digest
  let forsRoot ← forsRecover parts
  let root ← hypertreeRecover parts forsRoot
  return accept root

end SLHDSA.Scheme.Program
