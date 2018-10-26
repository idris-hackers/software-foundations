let

  fetchTarballFromGitHub =
    { owner, repo, rev, sha256, ... }:
    builtins.fetchTarball {
      url = "https://github.com/${owner}/${repo}/tarball/${rev}";
      inherit sha256;
    };

  fromJSONFile = f: builtins.fromJSON (builtins.readFile f);

in

{ nixpkgs ? fetchTarballFromGitHub (fromJSONFile ./nixpkgs-src.json) }:

with import nixpkgs {
  overlays = [
    (self: super: {
      ghc-with-pandoc = super.haskellPackages.ghcWithPackages (ps: with ps; [
        pandoc
      ]);

      idris = with super.idrisPackages; with-packages [
        base
        prelude
        pruviloj
      ];

      xelatex = super.texlive.combine {
        inherit (super.texlive) scheme-small
          amsmath
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
          mfirstuc
          minted
          newunicodechar
          substr
          todonotes
          xetex
          xfor
          xindy
          xstring;
      };
    })
  ];
};

stdenv.mkDerivation rec {
  name = "software-foundations-${version}-env";
  version = builtins.readFile ./VERSION;
  src = ./.;

  FONTCONFIG_FILE = makeFontsConf {
    fontDirectories = [
      iosevka
    ];
  };

  buildInputs = [
    ghc-with-pandoc
    idris
    python3Packages.pygments
    xelatex
    which
  ];

 installFlags = [
    "PREFIX=$(out)"
  ];

  meta = with stdenv.lib; {
    description = "Software Foundations in Idris";
    homepage = https://idris-hackers.github.io/software-foundations;
    license = licenses.mit;
    maintainers = with maintainers; [ yurrriq ];
    inherit (ghc.meta) platforms;
  };
}
