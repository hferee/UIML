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

doc: makefile.coq
	rm -fr html docs/*
	COQDOCEXTRAFLAGS='--external $(PUBLIC_URL)'
	@$(MAKE) -f makefile.coq html
	cp $(EXTRA_DIR)/resources/* html/* docs

-include makefile.coq

clean::
	rm makefile.coq makefile.coq.conf
	rm -f $(BUILD_FILES)

demo: theories/extraction/extraction.vo
	cd theories/extraction; cabal run

.PHONY: _
