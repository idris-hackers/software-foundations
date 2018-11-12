# Installing prerequisites on macOS

We assume that you are using a fresh macOS installation.

## Install [Homebrew](http://brew.sh/) package manager

```shell
/usr/bin/ruby -e "$(curl -fsSL https://raw.githubusercontent.com/Homebrew/install/master/install)"
```

## Install major dependencies via Homebrew

```shell
brew install idris cabal-install git ghc python wget
```

## Install [MacTeX](http://www.tug.org/mactex/) via Homebrew

```shell
brew cask install mactex
```

## Install pandoc and pandoc-types via cabal

```shell
cabal update
cabal install pandoc pandoc-types
export PATH=$HOME/.cabal/bin:$PATH
```

You might want to add cabal to your `PATH` permanently.

## Install pygments

```shell
pip install --user Pygments
```

## Install Iosevka font

Download the [Iosevka font](https://be5invis.github.io/Iosevka/) and put the `ttf`-files into `/Library/Fonts` directory.
Reboot to let macOS find the font.
