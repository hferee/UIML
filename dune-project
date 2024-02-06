(lang dune 3.0)

(name uiml)

(generate_opam_files true)

(source
 (github hferee/UIML))

(authors "Hugo Férée & Ian Shillito")

(maintainers "Hugo Férée")

(license MIT)

(documentation https://url/to/documentation)

(using coq 0.3)

(package
 (name uiml)
 (synopsis "Propositional quantifiers for modal logics formalized")
 (description "")
 (depends ocaml dune coq-color coq-stdpp js_of_ocaml)
 (tags
  (coq "intuitionistic logic" "proof theory" "propositional quantifiers" "extraction")))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/dune-files.html#dune-project
