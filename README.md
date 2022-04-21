# `coq-tinyram`

This implements a fully formalized virtual machine for the (Harvard) TinyRam architecture.

Future plans are to extend it with an assembler and compiler from some more abstract imperative language, and C, eventually.

`TinyRam` description: `papers/TinyRAM-spec-2.000.pdf`

## Build and launch emacs or vscodium with coq available, for an interactive session

1. [Install `nix`](https://nixos.org/download.html)
2. `nix develop .#emacs` or `nix develop .#vscodium`
3. Run `emacs` or `codium` from your terminal, either will now be available in
   your environment, for the duration of the shell.

## Get a development environment in a shell, without using emacs or vscodium


1. `nix develop`

## Compile `.v` files

```sh
dune build
```

Note that this can take in excess of 30 minutes, depending on your system. This will also create a new copy of `Tinyram_VM.hs`, extracted from the Coq files, within the `_build` directory, a copy of which can be found in the `src` folder.

## Compile `.hs` files

```sh
cabal new-build
```

and they can be run with

```sh
cabal new-run
```

## Mess around

Open up one of `theories/*.v` and type `C-c C-ENTER` to start the interactive session. Recall that `C-` is emacs-speak for holding the `CTRL` key.

## Customize

Explore `nix/doom.d/*` to get a feel for what tools you've been given and things you might want to change, disable, or add.
