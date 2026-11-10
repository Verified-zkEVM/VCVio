# Interop with external verification tools

[`Interop/README.md`](../../Interop/README.md) describes the package, its modules and what is left.
The rules for agents:

- **Requires go in `Interop/lakefile.toml`, never in the root `lakefile.lean`.** Every package that
  requires VCVio resolves every root `require`, so a tool's Lean library there would reach ArkLib,
  CatCrypt and every other dependent. A bridge with no Lake dependency of its own may build in the
  root package.
- **Pins move with the root.** `Interop/` shares the root's dependency cache, so its Lean, Mathlib
  and transitive pins must equal the root's. hax's pin (`a045d15a`) brings Aeneas through the fork
  hax requires. Move it with `lake update hax mathlib` from `Interop/`, never a bare `lake update`.
- **Isolation in both directions.** Core libraries never import `Interop.…`, `Hax.…` or
  `Aeneas.…`, and `Interop/**` never imports VCVio's own clients. Run
  `scripts/check-interop-isolation.sh` after changing imports.
- **One lift for Rust.** hax and Aeneas share `Aeneas.Std.RustM`. Lift Rust code into VCVio with
  `Interop.Rust.liftRustM`, and do not add a second adapter per tool.
- **Specifications go to `Std.WP`.** Core deprecated the `Std.Do` proof mode, while Aeneas and
  hax still emit `Std.Do`. Carry their facts into VCVio with `Interop.Rust.Triple`
  (`Spec.liftRustM` for `vcgen`, the `triple_liftRustM_of_*` transports otherwise), and do not
  import VCVio's `Std.Do` bridges here. VCVio's own driver takes the bare `vcgen` syntax, so call
  core's as `vcgen []` or `vcgen [lemmas]`.
- **Extracted code.** A module holding hax or Aeneas output names its Rust source and states
  whether the code was emitted by the tool or transcribed.
- **Building.** `cd Interop && lake build`. The `InteropRust` library lists its roots; add a module
  there once it builds, and add it to the axiom-sweep step of CI's `Interop Bridges` job.
