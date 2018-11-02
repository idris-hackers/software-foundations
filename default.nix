let

  fetchTarballFromGitHub =
    { owner, repo, rev, sha256, ... }:
    builtins.fetchTarball {
      url = "https://github.com/${owner}/${repo}/tarball/${rev}";
      inherit sha256;
    };

  fromJSONFile = f: builtins.fromJSON (builtins.readFile f);

  genMeta = { ghc, stdenv, ...}: with stdenv.lib; {
    description = "Software Foundations in Idris";
    homepage = https://idris-hackers.github.io/software-foundations;
    license = licenses.mit;
    maintainers = with maintainers; [ yurrriq ];
    inherit (ghc.meta) platforms;
  };

in

{ nixpkgs ? fetchTarballFromGitHub (fromJSONFile ./nixpkgs-src.json) }:

with import nixpkgs {
  overlays = [
    (self: super: {
      idrisPackages = super.idrisPackages // {
        software_foundations = with super.idrisPackages; build-idris-package {
          name = "software_foundations";
          version = builtins.readFile ./VERSION;
          src = ./.;
          idrisDeps = [ pruviloj ];
          meta = genMeta super;
        };
      };
    })
    (self: super: {
      idris = with super.idrisPackages; with-packages [
        base
        prelude
        pruviloj
        software_foundations
      ];

      pandoc = super.haskellPackages.ghcWithPackages (ps: with ps; [
        pandoc
      ]);

      inherit (super.pythonPackages) pygments;

      xelatex = super.texlive.combine {
        inherit (super.texlive) scheme-small
          amsmath
          biber
          biblatex
          datatool
          dirtytalk
          ebproof
          fontspec
          framed
          fvextra
          glossaries
          ifplatform
          latexmk
          lm-math
          logreq
          mfirstuc
          minted
          newunicodechar
          outlines
          substr
          todonotes
          tracklang
          xetex
          xfor
          xindy
          xstring;
      };
    })
  ];
};


stdenv.mkDerivation rec {
  name = "sf-idris-${version}";
  version = builtins.readFile ./VERSION;
  src = ./.;

  FONTCONFIG_FILE = makeFontsConf { fontDirectories = [ iosevka ]; };

  patchPhase = lib.optionalString (! lib.inNixShell) ''
    patchShebangs src/pandoc-minted.hs
  '';

  nativeBuildInputs = [
    pandoc
    pygments
    xelatex
    which
  ];

  buildInputs = [
    idris
  ];

  makeFlags = [ "PREFIX=$(out)" ];

  dontInstall = true;

  meta = (genMeta pkgs) // {
    platforms = lib.platforms.linux;
  };
}
