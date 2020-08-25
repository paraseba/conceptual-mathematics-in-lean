{pkgs ? (import <nixpkgs> {}) }:

let mathlib = import (builtins.fetchTarball {url = "https://github.com/leanprover-community/mathlib-tools/archive/master.tar.gz";}) {inherit pkgs;} ;
    vscode = pkgs.vscode-with-extensions.override {
      vscodeExtensions =
          with pkgs.vscode-extensions; [
            vscodevim.vim
          ]  ++

          pkgs.vscode-utils.extensionsFromVscodeMarketplace [
            {
              name = "lean";
              publisher = "jroesch";
              version = "0.16.12";
              sha256 = "1d88mz7msw23s0ggn829p8n3p0riwap07dk4hj31k38mv0h90rpc";
            }
          ] ;
    };
in
  pkgs.mkShell {
    buildInputs = with pkgs; [mathlib  elan vscode git];
  }
