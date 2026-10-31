/-
Copyright (c) 2026 Tom Wambsgans, Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans, Alexander Hicks
-/

module
public import Init

/-!
# Pure-mode signature requests

Requests retain the message and context as separate byte strings. This data module selects
no signing algorithm, oracle interpreter, experiment or resource policy.
-/

public section

namespace SLHDSA.SHAKE128s

/-- Byte strings. -/
abbrev Bytes := List UInt8

/-- A signing request: message and context. -/
structure Message where
  /-- The message. -/
  message : Bytes
  /-- The context string. -/
  context : Bytes
deriving DecidableEq

end SLHDSA.SHAKE128s
