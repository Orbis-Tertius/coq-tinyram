# Goal: Compiling C to vnTinyRAM

Bottleneck: CompCert license (we originally wanted to leverage a CompCert IR)

Current plan: advance the `vnTinyRAM` emulator in coq, figure out the rest of it later. 

`vnTinyRam` description: `papers/TinyRAM-spec-2.000.pdf`

## Ready your machine

using `home-manager` and `nix-direnv`: 
1. you need `doom.d/` seed contents, with two important properties
   - `(doom! ... :lang ... coq)` in `doom.d/init.el`
   - `(custom-set-variables <backtick>(coq-prog-name "coqtop"))` in `doom.d/config.el`, where the backtick is the standard backtick I can't type because markdown. 
     - Note: typically `coq-prog-name` deals in absolute paths, but we're going to get emacs talking to `nix-direnv` later so it all works out this way. 
2. [`nix-doom-emacs`](https://github.com/vlaci/nix-doom-emacs#getting-started). `Doom` is a vim-based emacs build/config that let's you declaratively install `proof general`, which is the interactive frontend to `coq`. 
3. install `nix-direnv`. 
4. `ocaml` and `dune_2` in `home.nix` packages. 
5. the following file `coq.nix` 
```nix
{ pkgs ? import <nixpkgs> {} }:
pkgs.mkShell {
  buildInputs = with pkgs.coqPackages; [
    coq
    coq-ext-lib
    ITree
  ];
}
```
6. the following file `.envrc`
```
use nix coq.nix
```
7. (uncertain) `(package! envrc)` in `doom.d/packages.el` 

Do your `home-manager switch`. 

## Build

``` sh
dune build
```

## Fire it up

Open up one of the `theories/*.v` files, type `C-c C-ENTER`, and cross your fingers. 
