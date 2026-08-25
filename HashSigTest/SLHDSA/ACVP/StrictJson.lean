/-
Copyright (c) 2019 Gabriel Ebner. All rights reserved.
Modifications copyright (c) 2026 Nicolas Consigny.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Marc Huisinga; modified by Nicolas Consigny
-/

module
public import Lean.Data.Json.Parser

/-!
# Duplicate-rejecting JSON parser for ACVP evidence

Lean's ordinary JSON parser stores object fields in a tree map and therefore overwrites duplicate
keys. ACVP evidence is parsed fail-closed: this small Apache-licensed adaptation of Lean's parser
rejects a key before insertion when it already occurs in the current object.
-/

public section

open Std.Internal.Parsec
open Std.Internal.Parsec.String

namespace SLHDSA.Test.ACVP.StrictJson

open Lean

mutual

  private partial def arrayCore (acc : Array Json) : Parser (Array Json) := do
    let head ← anyCore
    let acc := acc.push head
    let c ← any
    if c == ']' then
      ws
      return acc
    else if c == ',' then
      ws
      arrayCore acc
    else
      fail "unexpected character in array"

  private partial def objectCore (fields : Std.TreeMap.Raw String Json) :
      Parser (Std.TreeMap.Raw String Json) := do
    Lean.Json.Parser.lookahead (· == '"') "\""
    skip
    let key ← Lean.Json.Parser.str
    ws
    Lean.Json.Parser.lookahead (· == ':') ":"
    skip
    ws
    if fields.contains key then
      fail s!"duplicate object key: {key}"
    let value ← anyCore
    let fields := fields.insert key value
    let c ← any
    if c == '}' then
      ws
      return fields
    else if c == ',' then
      ws
      objectCore fields
    else
      fail "unexpected character in object"

  private partial def anyCore : Parser Json := do
    let c ← peek!
    if c == '[' then
      skip
      ws
      if (← peek!) == ']' then
        skip
        ws
        return .arr #[]
      return .arr (← arrayCore #[])
    else if c == '{' then
      skip
      ws
      if (← peek!) == '}' then
        skip
        ws
        return .obj ∅
      return .obj (← objectCore ∅)
    else if c == '"' then
      skip
      let value ← Lean.Json.Parser.str
      ws
      return .str value
    else if c == 'f' then
      skipString "false"
      ws
      return .bool false
    else if c == 't' then
      skipString "true"
      ws
      return .bool true
    else if c == 'n' then
      skipString "null"
      ws
      return .null
    else if c == '-' || ('0' ≤ c && c ≤ '9') then
      let value ← Lean.Json.Parser.num
      ws
      return .num value
    else
      fail "unexpected input"

end

/-- Parse one JSON value and reject duplicate keys at every object nesting depth. -/
def parse (source : String) : Except String Lean.Json :=
  Parser.run (do ws; let result ← anyCore; eof; return result) source

end SLHDSA.Test.ACVP.StrictJson
