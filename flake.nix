{
  inputs = {
    nixpkgs.url = "nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };
  
  outputs = { self, nixpkgs, flake-utils }: flake-utils.lib.eachDefaultSystem (system:
    let
      pkgs = nixpkgs.legacyPackages.${system};
      main = coqPackages: with pkgs; with coqPackages;
        mkCoqDerivation {
          pname = "num-analysis";
          version = "1.0";
          src = ./.;
          propagatedBuildInputs = [ coquelicot flocq mathcomp mathcomp-classical mathcomp-ssreflect ];          
        }
      ;
    in {
      packages = with pkgs; rec {
        num-analysis_8_16 = main coqPackages_8_16;
        num-analysis_8_17 = main coqPackages_8_17;
        num-analysis_8_18 = main coqPackages_8_18;
        num-analysis = num-analysis_8_16;
        default = num-analysis;
      };
    });
}
