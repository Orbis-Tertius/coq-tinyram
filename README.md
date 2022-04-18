# `coq-tinyram`

Current plan: advance the `vnTinyRAM` emulator in coq, figure out the rest of it later.

`vnTinyRam` description: `papers/TinyRAM-spec-2.000.pdf`

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

## Mess around

Open up one of `theories/*.v` and type `C-c C-ENTER` to start the interactive session. Recall that `C-` is emacs-speak for holding the `CTRL` key.

## Customize

Explore `nix/doom.d/*` to get a feel for what tools you've been given and things you might want to change, disable, or add.
