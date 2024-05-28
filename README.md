PathORAM.

## Build Instructions

The simplest way to build this repo is by using opam and dune:
```
opam repo add coq-released https://coq.inria.fr/opam/released
opam install . --deps-only
dune build
```

To generate a `_CoqProject` for your editor:

```
./configure.sh
```
