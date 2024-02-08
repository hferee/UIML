EXTRA_DIR:= doc-config
COQDOCFLAGS:= \
  --toc --toc-depth 2 --html --interpolate \
	-d docs \
  --index indexpage --no-lib-name --parse-comments \
  --with-header $(EXTRA_DIR)/header.html --with-footer $(EXTRA_DIR)/footer.html
export COQDOCFLAGS
PUBLIC_URL="https://hferee.github.io/UIML"
SUBDIR_ROOTS := theories
DIRS := . $(shell find $(SUBDIR_ROOTS) -type d)
BUILD_PATTERNS := *.vok *.vos *.glob *.vo
BUILD_FILES := $(foreach DIR,$(DIRS),$(addprefix $(DIR)/,$(BUILD_PATTERNS)))

_: makefile.coq

makefile.coq:
	coq_makefile -f _CoqProject -docroot docs -o $@


doc: makefile.coq demo
	rm -fr html docs/*
	COQDOCEXTRAFLAGS='--external $(PUBLIC_URL)'
	@$(MAKE) -f makefile.coq html
	cp html/* _build/default/bin/uiml_demo.bc.js docs
	cp $(EXTRA_DIR)/resources/* docs

-include makefile.coq

clean::
	rm makefile.coq makefile.coq.conf
	rm -f $(BUILD_FILES)
	rm -f extraction/*.ml extraction/*.mli

# OCaml build
#SOURCE_ROOT=extraction
#BUILD_PATTERNS := *.ml *.mli
#SOURCES=$(addprefix $(SOURCE_ROOT)/,$(BUILD_PATTERNS))
#RESULT=extraction/UIML_extraction

demo: extraction/UIML_extraction.vo bin/uiml_demo.ml
	dune build


#-include OCamlMakefile

.PHONY: _
