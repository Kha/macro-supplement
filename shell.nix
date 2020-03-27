{ pkgs ? import ./lean4/nix/nixpkgs.nix }:

let
  shell = import ./lean4/shell.nix {};
  lean-shell = pkgs.mkShell {
    buildInputs = [ shell.lean ];
  };
in lean-shell // {
  emacs = pkgs.mkShell {
    shellHook = ''
${shell.emacs}/bin/emacs Examples.lean
exit 0
    '';
  };
}
