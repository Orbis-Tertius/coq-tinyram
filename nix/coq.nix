{ pkgs ? import <nixpkgs> {} }:
pkgs.mkShell {
  buildInputs = with pkgs.coqPackages; [
    coq
    coq-ext-lib
    ITree
  ];
}
