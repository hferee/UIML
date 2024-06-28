(lang dune 3.8)

(name uiml)

(generate_opam_files true)

(source
 (github hferee/UIML))

(authors "Hugo Férée"
         "Iris van der Giessen"
         "Sam van Gool"
         "Ian Shillito")

(maintainers "Hugo Férée")

(license CecILL)

(homepage https://hferee.github.io/)
(documentation https://hferee.github.io/UIML/toc.html)

(using coq 0.8)

(package
 (name uiml)
 (synopsis "Propositional quantifiers for modal logics formalised")
 (description "")
 (allow_empty)
 (depends ocaml dune coq-stdpp js_of_ocaml angstrom exenum)
 (tags
  (coq "intuitionistic logic" "proof theory" "propositional quantifiers" "extraction")))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/dune-files.html#dune-project
