# Expert report scaffold

`slhdsa-formalization-audit.tex` is the canonical editable report. There is **no fixed length limit**;
clarity, validated detail, and traceability control length. The scaffold deliberately distinguishes
normative conformance, abstract security, executable regression, and deployment refinement.

Build with:

```text
latexmk -pdf -interaction=nonstopmode -halt-on-error slhdsa-formalization-audit.tex
```

Generated PDF/auxiliary files are local build artifacts. Findings and tables must be generated or
checked against `../matrices/**` before final publication. R16's F-061/F-062 repair uses
constant/count-only cleanup evidence, duplicate-owner preflight, and an exact scoped AST lifecycle
inventory. Independent r16 accepted S01. The reviewed machinery is frozen and future sessions
center on Lean deliverables unless a concrete regression requires reopening it.

focused-parser-partition: legacy=8; source-object-link=21; imports=4; sha-output-binding=9; path-cli=20; output-types=2; artifacts=130; wrong-srcdir=2; stale=2; fresh-root=5; query-output=5; replacement-cache=3; descriptor-lifecycle=6; descriptor-ownership=17; total=234; sha-cli-is-subset-of-path-cli=6; nominal-success-excluded=true
