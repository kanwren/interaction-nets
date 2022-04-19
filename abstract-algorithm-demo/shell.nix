with import <nixpkgs> {};

mkShell {
  buildInputs = [
    rustup
    wasm-pack
    wasm-bindgen-cli
    pkgconfig
    openssl
    nodejs_latest
  ];
  LD_LIBRARY_PATH="${stdenv.cc.cc.lib}/lib64";
}
