{ pkgs ? import <nixpkgs> {} }:
pkgs.mkShell {
  buildInputs = with pkgs.coqPackages; [
    ocaml
    dune_2
    coq
    coq-ext-lib
    ITree
  ];
}
