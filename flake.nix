{
  description = "Lambda executor";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    crane.url = "github:ipetkov/crane";
    flake-utils.url = "github:numtide/flake-utils";
    rust-overlay = {
      url = "github:oxalica/rust-overlay";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };


  outputs = { self, nixpkgs, crane, flake-utils, rust-overlay, ... }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs {
          inherit system;
          overlays = [ (import rust-overlay) ];
        };

        inherit (pkgs) lib;

        rustToolchain = pkgs.rust-bin.selectLatestNightlyWith (toolchain: toolchain.default.override {
          extensions = [ "rust-src" ];
        });

        craneLib = ((crane.mkLib pkgs).overrideToolchain rustToolchain);

        src = lib.cleanSourceWith {
          src = ./.;
          filter = path: type: (craneLib.filterCargoSources path type);
        };
        cliArgs = {
          inherit src;
          strictDeps = true;
          buildInputs = [ ];

          pname = "lambxekutor_cli";
          cargoExtraArgs = ''--package=lambxekutor_cli'';
        };

        cliArtifacts = craneLib.buildDepsOnly cliArgs;
        cliCrate = craneLib.buildPackage (
          cliArgs // {
            cargoArtifacts = cliArtifacts;
          }
        );
      in
      {
        checks = {
          lambxekutorCrate = cliCrate;
          lambxekutorCliFmt = craneLib.cargoFmt cliArgs;
          lambxekutorCliClippy = {
            inherit src;
            cargoArtifacts = cliArtifacts;

            cargoClippyExtraArgs = "-- --deny warnings";
          };
        };

        packages.default = cliCrate;

        apps.default = flake-utils.lib.mkApp {
          drv = cliCrate;
        };

        devShells.default = craneLib.devShell {
          checks = self.checks.${system};

          packages = with pkgs; [
            rustToolchain
            rust-analyzer

            cargo-flamegraph
            cargo-outdated
          ];
        };
      }
    );
}
