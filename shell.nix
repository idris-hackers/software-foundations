{ nixpkgs ? import <nixpkgs> {}
, compiler ? "ghc802"
}:


let
  inherit (nixpkgs) pkgs;
  ghc = pkgs.haskell.packages."${compiler}".ghcWithPackages (ps: with ps; [
    pandoc
  ]);
  # FIXME: TeX Live is pretty much broken in Nix right now.
  # xelatex = pkgs.texlive.combine {
  #   inherit (pkgs.texlive) scheme-small xetex latexmk todonotes;
  # };
in

pkgs.stdenv.mkDerivation {
  name = "software-foundations-env";

  buildInputs = [ ghc ];
    # TODO:
    # [ ghc xelatex ] ++
    # (with pkgs; [ python3 ]) ++
    # (with pkgs.python35Packages; [ pygments ]);
}
