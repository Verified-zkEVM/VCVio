# Interop with external verification tools

[`Interop/README.md`](../../Interop/README.md) is the index of the sub-projects and states the
rules they share; each sub-project's README states its trusted base, assumptions and coverage. The
rules for agents:

- **One sub-project per trusted base.** A sub-project is a directory `Interop/<Sub>/` with its own
  Lake package, `lakefile.toml`, and modules named `Interop.<Sub>.…`. Code that uses a
  sub-project's tools goes in that sub-project. Tools with another trusted base get a new
  sub-project, whose README follows the index's template; CI finds the directory by itself.
- **Requires go in the sub-project's lakefile, never in the root `lakefile.lean`.** Every package
  that requires VCVio resolves every root `require`, so a tool's Lean library there would reach
  ArkLib, CatCrypt and every other dependent.
- **Pins move with the root.** A sub-project that shares the root's dependency cache keeps its
  Lean, Mathlib and transitive pins equal to the root's. In `Interop/Aeneas`, hax's pin
  (`a045d15a`) brings Aeneas through the fork hax requires; move it with `lake update hax mathlib`
  from `Interop/Aeneas/`, never a bare `lake update`.
- **Isolation.** Core libraries never import `Interop.…`, `Hax.…` or `Aeneas.…`, and `Interop/**`
  never imports VCVio's own clients. A sub-project imports another only through a `require` of
  that sub-project's package, with the pair listed in `scripts/interop_import_allowlist.txt`. Run
  `scripts/check-interop-isolation.sh` after changing imports.
- **Generic code goes to VCVio or PolyFun first,** never into one sub-project for another to
  import.
- **One lift for Rust.** hax and Aeneas share `Aeneas.Std.RustM`. Lift Rust code into VCVio with
  `Interop.Rust.liftRustM` (in `Interop.Aeneas.Lift.RustM`), and do not add a second adapter per
  tool.
- **Specifications go to `Std.WP`.** Core deprecated the `Std.Do` proof mode, while Aeneas and
  hax still emit `Std.Do`. Carry their facts into VCVio with `Interop.Aeneas.Lift.Triple`
  (`Spec.liftRustM` for `vcgen`, the `triple_liftRustM_of_*` transports otherwise). A bare
  `vcgen` is core's tactic; VCVio's own driver is `pvcgen`.
- **Extracted code.** A module holding hax or Aeneas output names its Rust source and states
  whether the code was emitted by the tool or transcribed.
- **Rules of Squirrel's logic.** In `Interop/Squirrel`, a new rule of the logic adds its row to
  the rules table of [the design record](../design/interop-squirrel.md), and a row to its
  obligations table for each modelling choice it makes. A rule whose proof needs the class of
  machines to admit a reduction adds that field to `AdvClass` together with the construction it
  admits, and proves that `AdvClass.all` meets it.
- **Building.** `cd Interop/<Sub> && lake build`. The libraries in the lakefile's `defaultTargets`
  list their roots; add a module there once it builds, and CI's `Interop <Sub>` job sweeps it for
  axioms.
