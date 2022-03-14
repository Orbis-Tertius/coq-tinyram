{ pkgs ? import <nixpkgs> {} }:
pkgs.mkShell {
  buildInputs = with pkgs.coqPackages; [
    pkgs.ocaml
    pkgs.dune_2
    coq
    coq-ext-lib
    ITree
  ];
}
