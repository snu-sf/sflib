# sflib
A collection of useful Rocq tactics.

Compatibility: Rocq versions 8.20 and newer.

## Installation
You have two options to install sflib:

- Using a Local Clone:
  ```sh
  opam install .
  ```

- From the opam Repository:
  ```sh
  opam remote add coq-sflib -k git https://github.com/snu-sf/sf-opam-coq-archive
  opam install coq-sflib
  ```

## Build
After installation, build sflib with:

```sh
dune build @install
```

## For VSCoq
- Use `make` to create `_CoqProject` file.