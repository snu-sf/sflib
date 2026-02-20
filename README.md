# sflib

A collection of useful Rocq lemmas and tactics for proof automation and rewriting.

## Compatibility

| Branch   | Rocq/Coq version |
|----------|-------------------|
| `master` | Rocq >= 9.0       |
| `8.20`   | Coq >= 8.19.2     |

## Installation

```sh
git clone https://github.com/snu-sf/sflib.git
cd sflib
opam install .
```

## Usage

```coq
From sflib Require Import sflib.
```

## Build

```sh
dune build
```

## License

BSD-2-Clause
