#!/bin/sh

opam repo add coq-released https://coq.inria.fr/opam/released "$@"
opam pin coq 8.20.1 "$@"
opam install coq coq-stdpp coq-equations angstrom js_of_ocaml js_of_ocaml-ppx exenum "$@"
