let
  pkgs = import <nixpkgs> {};
in
with pkgs; mkShell {
  nativeBuildInputs = [ idris2 idris2Packages.idris2Lsp rlwrap ];
}
