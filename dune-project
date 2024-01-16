(lang dune 3.8)

(name uiml)

(generate_opam_files true)

(source
 (github hferee/UIML))

(authors "Hugo Férée ; Ian Shillito")

(maintainers "Hugo Férée ; Ian Shillito")

(license MIT)

(documentation https://TODO)

(using coq 0.8)

(package
 (name uiml)
 (allow_empty)
 (synopsis "Uniform Interpolation for Modal Logics")
 (description "A formalization in Coq of uniform interpolation theorems for
              logics K, GL and iSL")
 (depends ocaml dune exenum coq-color coq-stdpp)
 (tags
  (coq "intuitionistic logic" "proof theory" "propositional quantifiers"
       "extraction" "modal logic")))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/dune-files.html#dune-project
