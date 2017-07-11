{ nixpkgs ? import <nixpkgs> {}
, compiler ? "ghc802"
}:

let
  inherit (nixpkgs) pkgs;

  haskellPackages = pkgs.haskell.packages."${compiler}";
  ghc = haskellPackages.ghcWithPackages (ps: with ps; [
    idris
    pandoc
  ]);
  # FIXME: TeX Live is pretty much broken in Nix right now.
  # xelatex = pkgs.texlive.combine {
  #   inherit (pkgs.texlive) scheme-small xetex latexmk todonotes;
  # };
in

pkgs.stdenv.mkDerivation rec {
  name = "software-foundations-${version}-env";
  version = "0.0.1.0";

  src = ./.;

  # TODO: xelatex
  buildInputs = [ ghc ] ++
    (with pkgs; [ python3 ]) ++
    (with pkgs.python35Packages; [ pygments ]);

  meta = with pkgs.stdenv.lib; {
    description = "Software Foundations in Idris";
    # TODO: longDescription
    homepage = http://idris-hackers.github.io/software-foundations;
    # TODO: license
    maintainers = with maintainers; [ yurrriq ];
    inherit (ghc.meta) platforms;
  };
}
