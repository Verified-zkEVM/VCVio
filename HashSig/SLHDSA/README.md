# SLH-DSA

Use the [FIPS 205 source guide](../../docs/agents/slh-dsa.md) to locate an algorithm by its number in the standard, choose a security theorem by its resource assumptions, or reproduce a vector check.

For the arbitrary-depth construction, start with [the internal algorithms](GeneralScheme.lean) and [the external signing and verification interface](External.lean). The security results have separate entry points for [all six SHAKE profiles](Security/Wire.lean) and [deterministic SHAKE-128s with an actual-work budget](SHAKE128s/Statement/Theorems/StrongUnforgeability.lean).
