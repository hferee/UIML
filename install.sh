#!/bin/sh

opam repo add coq-released https://coq.inria.fr/opam/released
opam pin coq 8.19.1
opam install coq coq-stdpp

