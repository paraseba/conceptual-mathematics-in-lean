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
              version = "0.16.13";
              sha256 = "0f31kchj427jlrc7rhvvypsn6mixm7pf18xx215zqp2s82nnvcny";
            }
          ] ;
    };
in
  pkgs.mkShell {
    buildInputs = with pkgs; [mathlib  elan vscode git];
  }
