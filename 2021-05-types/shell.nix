{ nixpkgs ? import <nixpkgs> {}
}:
nixpkgs.mkShell {

    buildInputs = [
        (nixpkgs.agda.withPackages (p: [
            p.cubical
            p.standard-library
        ]))
        nixpkgs.coq
        nixpkgs.idris2
        nixpkgs.rlwrap
    ];

    name = "2021-05-types";

}
