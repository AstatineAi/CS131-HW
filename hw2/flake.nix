{
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  };

  outputs =
    { nixpkgs, ... }:
    let
      system = "x86_64-linux";
      pkgs = nixpkgs.legacyPackages.${system};
    in
    {
      devShells.${system}.default = pkgs.mkShell {
        packages =
          with pkgs;
          [
            gnumake
            zip
          ]
          ++ (with ocaml-ng.ocamlPackages_4_14; [
            dune_3
            num
            ocaml
            utop
          ]);
      };

      formatter.${system} = pkgs.nixfmt-rfc-style;
    };
}
