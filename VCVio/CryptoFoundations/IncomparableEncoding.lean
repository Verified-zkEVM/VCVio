/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import VCVio.CryptoFoundations.IncomparableEncoding.Basic
public import VCVio.CryptoFoundations.IncomparableEncoding.NonMaximum
public import VCVio.CryptoFoundations.IncomparableEncoding.Error
public import VCVio.CryptoFoundations.IncomparableEncoding.Retry

/-!
# Incomparable encodings

Arbitrary global incomparable codes, fallible encoding, explicit sampling error and bounded retry
observations. Collision security and concrete code families have separate interfaces.
-/
