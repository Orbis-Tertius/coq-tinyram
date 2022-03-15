{
  description = "A flake for building vscodium with vscoq";

  inputs.nixpkgs.url = "nixpkgs";
  inputs.flake-utils.url = "github:numtide/flake-utils";

  outputs = { self, nixpkgs, flake-utils }: flake-utils.lib.simpleFlake {
    inherit self nixpkgs;
    name = "vsc";
    preOverlays = [  ];
    systems = [ "x86_64-linux" "x86_64-darwin" ];
    config = {
      allowUnsupportedSystem = true;
    };
    overlay = final: prev: {
      vsc = with final; rec {
        env = [ ];

        wrapper = vscode-with-extensions.override {
          vscode = vscodium;
          vscodeExtensions = with vscode-extensions; 
            vscode-utils.extensionsFromVscodeMarketplace [
            {
              name = "VSCoq";
              publisher = "maximedenes";
              version = "0.3.6";
              sha256 = "sha256-b0gCaEzt5yAj53oLFZSXSD3bum9J1fYes/uf9+OlUek=";
            }
          ];
        };

	      codium = stdenv.mkDerivation {
                pname = "codium";
                version = "1.0";
                phases = ["installPhase"];
                installPhase = ''
                  mkdir -p $out/bin;
                  makeWrapper ${wrapper}/bin/codium $out/bin/codium --prefix PATH : ${lib.makeBinPath env}
                '';
                buildInputs = [ makeWrapper ];
              };

        defaultPackage = codium;
      };
    };
  };
}
