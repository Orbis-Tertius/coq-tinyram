{
  description = "Write coq in doom for the coq-tinyram project";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixos-unstable";
    nix-doom-emacs.url = "github:nix-community/nix-doom-emacs";
    emacs.url = "github:cmacrae/emacs";
    flake-utils.url  = "github:numtide/flake-utils";
  };

  outputs =
    { self
    , nixpkgs
    , emacs
    , flake-utils
    , nix-doom-emacs
    , ocaml
    , dune_2
    }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        overlays = [ (import emacs) ];
        pkgs = import nixpkgs {
          inherit system overlays;
        };
      in
      with pkgs;
      {
        defaultPackage = nix-doom-emacs.package.${system} { doomPrivateDir = ./nix/doom.d; };
      }
    );
}
