/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import HashSig.SLHDSA.Security.SchemeGames

/-!
# Signature bundle consumers through public equations

These ordinary-import consumers use an opaque algorithm bundle in a composed program and
retain its perfect-completeness theorem. The projection test also checks that the public
equation is available without making the implementation a downstream reducer.
-/

public section

open SLHDSA SLHDSA.Security

variable {vp : ValidatedParams} (prims : Primitives vp.params)
  [SampleableType prims.SkSeed] [SampleableType prims.SkPrf]
  [SampleableType prims.PkSeed] [SampleableType prims.Y] [DecidableEq prims.Y]

example (pk : PublicKeyCore prims.core) (msg : List Byte)
    (sig : GeneralScheme.SignatureCore vp prims.core) :
    (generalAlg prims).verify pk msg sig =
      pure (GeneralScheme.verifyInternal vp prims (emptyContextMessage msg) sig pk) := by
  fail_if_success rfl
  rw [generalAlg_verify]

example (pk : PublicKeyCore prims.core) (msg : List Byte)
    (sig : GeneralScheme.SignatureCore vp prims.core) :
    (do
      let accepted ← (generalAlg prims).verify pk msg sig
      pure (!accepted)) =
        (pure (!(GeneralScheme.verifyInternal vp prims (emptyContextMessage msg) sig pk)) :
          ProbComp Bool) := by
  rw [generalAlg_verify]
  simp only [pure_bind]

example : (generalAlg prims).PerfectlyComplete ProbCompRuntime.probComp :=
  generalAlg_perfectlyComplete
