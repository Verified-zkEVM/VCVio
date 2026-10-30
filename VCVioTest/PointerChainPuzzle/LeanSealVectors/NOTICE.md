# leanSeal vector provenance and notice

`vectors.json` is an unchanged copy of `tests/vectors.json` from leanSeal
(<https://github.com/leanEthereum/leanSeal>), the leanSeal v1 test vectors of its specification,
section 10. The file was last changed in leanSeal commit
`6305f59a8aa2032527bee04b9d1879ac7f4f94c9`; its SHA-256 is
`9eeb2366433d15af094a773951fa28c9925e7fe9841c29709930c5d5a24e357b`. leanSeal regenerates it
byte for byte with `leanseal vectors`, and its Python reference checks it.

leanSeal is Copyright (c) 2026 its authors and is dual-licensed under the MIT license and the
Apache License, Version 2.0. The vectors are regression and conformance evidence only.

`VCVioTest/PointerChainPuzzle/LeanSeal.lean` reads the `cases` list and the `invalid` entries of
kind `puzzle`; the entries of kind `envelope`, `secret` and `checkpoint`, and the envelope,
secret, puzzle-identifier and checkpoint encodings of each case, are not checked.
