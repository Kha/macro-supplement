{ pkgs ? import ./lean4/nix/nixpkgs.nix }:

let
  lean = import ./lean4/default.nix {};
  lean4-mode = pkgs.emacsPackages.melpaBuild {
    pname = "lean4-mode";
    version = "1";
    src = ./lean4/lean4-mode;
    packageRequires = with pkgs.emacsPackages.melpaPackages; [ dash dash-functional f flycheck s ];
    propagatedUserEnvPkgs = [ lean ];
    recipe = pkgs.writeText "recipe" ''
      (lean4-mode :repo "leanprover/lean4" :fetcher github :files ("*.el"))
    '';
    patchPhase = ''
      sed -i 's/lean_wrapped/lean/' *.el
    '';
    fileSpecs = [ "*.el" ];
  };
  emacs = pkgs.emacsWithPackages (epkgs:
    # ???
    with pkgs.emacsPackages.melpaPackages; [ dash dash-functional f flycheck s ] ++ [ lean4-mode ]);
in pkgs.mkShell {
  buildInputs = with pkgs; [ lean ];
}
