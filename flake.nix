{
  description = "A Flake for building coq and providing devShells for the coq-tinyram project";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixos-unstable";
    nix-doom-emacs.url = "github:nix-community/nix-doom-emacs";
    emacs.url = "github:cmacrae/emacs";
  };

  outputs =
    { self
    , nixpkgs
    , emacs
    , nix-doom-emacs
    ,
    }:
    let
      # Generate a user-friendly version number.
      version = builtins.substring 0 8 self.lastModifiedDate;
      # System types to support.
      supportedSystems = [ "x86_64-linux" "aarch64-linux" ];
      # Helper function to generate an attrset '{ x86_64-linux = f "x86_64-linux"; ... }'.
      forAllSystems = nixpkgs.lib.genAttrs supportedSystems;
      # Nixpkgs instantiated for supported system types.
      nixpkgsFor = forAllSystems (system:
        import nixpkgs {
          inherit system;
          overlays = [ self.overlay ];
        });
    in
    {
      overlay = final: prev: { };
      devShells = forAllSystems (system:
        let
          pkgs = nixpkgsFor."${system}";
        in
        {
          defaultShell = pkgs.mkShell {
            buildInputs = with pkgs; [
              ocaml
              dune_2
              coqPackages.coq
              coqPackages.coq-ext-lib
              coqPackages.ITree
            ];
          };
          vscodium = self.devShells.${system}.defaultShell.overrideAttrs (old: {
            buildInputs =
              let
                vscodeWithCoq = pkgs.vscode-with-extensions.override {
                  vscode = pkgs.vscodium;
                  vscodeExtensions = pkgs.vscode-utils.extensionsFromVscodeMarketplace [
                    {
                      name = "VSCoq";
                      publisher = "maximedenes";
                      version = "0.3.6";
                      sha256 = "sha256-b0gCaEzt5yAj53oLFZSXSD3bum9J1fYes/uf9+OlUek=";
                    }
                  ];
                };
              in
              old.buildInputs
              ++ [
                vscodeWithCoq
              ];
          });
          emacs = self.devShells.${system}.defaultShell.overrideAttrs (old: {
            buildInputs =
              let
                doom-emacsWithCoq = nix-doom-emacs.package.${system} {
                  doomPrivateDir = ./nix/doom.d;
                };
              in
              old.buildInputs
              ++ [
                doom-emacsWithCoq
              ];
          });
        });
    };
}
