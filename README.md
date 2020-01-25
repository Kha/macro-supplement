# Supplemental material for the "Beyond Notations" paper

This repository contains the full bigop example (Appendix A, `Bigop.lean`), the example expander (`Expander.lean`),
and other examples from the paper (`Examples.lean`). It is pinned to a compatible Lean 4 commit via the `./lean4`
submodule (be sure to check it out via `git submodule update --init lean4`).

The recommended way of interacting with this supplement is via [Nix](https://nixos.org/nix/). After installing Nix,
`nix-shell` gives a shell with `lean` in the path after building it from `./lean4`, and
`nix-shell --run "emacs Examples.lean"` opens Emacs with the `lean4-mode` extension preconfigured.

Otherwise, please follow the instruction in `./lean4/doc/make/index.md`.
