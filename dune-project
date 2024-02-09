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

(source https://github.com/hferee/UIML)
(bug_reports https://github.com/hferee/UIML/issues)
(homepage https://hferee.github.io/)
(documentation https://hferee.github.io/UIML/toc.html)

(using coq 0.8)

(package
 (name uiml)
 (synopsis "Propositional quantifiers for modal logics formalised")
 (description "")
 (allow_empty)
 (depends ocaml dune coq-color coq-stdpp js_of_ocaml angstrom)
 (tags
  (coq "intuitionistic logic" "proof theory" "propositional quantifiers" "extraction")))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/dune-files.html#dune-project
