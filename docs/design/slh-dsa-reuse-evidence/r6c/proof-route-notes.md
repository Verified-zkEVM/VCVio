# Why two proof methods remain

Source-import map only, not a new audit of all probability proofs.

* General #766 `Security.CoverageBound` consumes `CoverageRun` and `JointBound`.
  Its role-run/tape-hit/witness argument and byte/seed/randomizer bounds remain
  the general construction proof, with its original structural cap predicates.
* `Statement.Theorems.StrongUnforgeability.slhDsa_sufCma_127` invokes
  `Bridge.Scheme` and `Proof.WorkFinal`. WorkFinal consumes the share joint
  accounting, filed/provenance route and WorkTarget; WorkTarget consumes the
  by-source target. This is the specialized probability-one actual joint-work
  proof, not a relabelled general structural bound.
* `MainTheorem.prEvent_runAll` bridges warmed/structural experiments; WarmedGame
  imports Presample and WholeGameStructural. This is the concrete location
  where C1/C3/C4 must be USED, without misreporting the projected warmup law
  as an exact cost/cache identity.
* ForsConcentrationSharper consumes the old moment theorem through the
  Poisson/disclosure route. C2 must change that actual production dependency,
  preserving all numerical certificates, rather than leave a useful generic
  theorem only in a test replica.
* R5 factors canonical execution definitions and their explicit representation
  bridges. It does not imply concentration/charge/provenance proof unification.

The finite extraction list leaves genuinely specialized side certificates local;
it still requires real shared proof ownership, actual scheme consumers and removal
of duplicate executable construction ownership. It is not a declaration that
51k original lines are all intrinsically specialized or cheaply factorizable.
