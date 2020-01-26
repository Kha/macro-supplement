# Supplemental material for the "Beyond Notations" paper

This repository contains the full bigop example (Appendix A, `Bigop.lean`), the example expander (Appendix B,
`Expander.lean`), and other examples from the paper (`Examples.lean`). It is pinned to a compatible Lean 4 commit via
the `./lean4` submodule (be sure to check it out via `git submodule update --init lean4`).

The recommended way of interacting with this supplement is via [Nix](https://nixos.org/nix/) (Linux, macOS). After
installing Nix, `nix-shell -A lean` gives a shell with `lean` in the path after building it from `./lean4`, and
`nix-shell -A emacs` opens Emacs with the `lean4-mode` extension preconfigured.

Otherwise, please follow the instruction in `./lean4/doc/make/index.md` for building Lean 4. To use `lean4-mode` in
Emacs, add the following to your `init.el`:
```
;; You need to modify the following line
(setq lean4-rootdir "/path/to/supplement/lean4")

(setq lean4-mode-required-packages '(dash dash-functional f flycheck s))

(require 'package)
(add-to-list 'package-archives '("melpa" . "http://melpa.org/packages/"))
(package-initialize)
(let ((need-to-refresh t))
  (dolist (p lean4-mode-required-packages)
    (when (not (package-installed-p p))
      (when need-to-refresh
        (package-refresh-contents)
        (setq need-to-refresh nil))
      (package-install p))))

(setq load-path (cons (concat lean4-rootdir "/lean4-mode") load-path))
(require 'lean4-mode)
```
