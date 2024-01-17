EXTRA_DIR:= doc-config
COQDOCFLAGS:= \
  --toc --toc-depth 2 --html --interpolate \
  --index indexpage --no-lib-name --parse-comments \
  --with-header $(EXTRA_DIR)/header.html --with-footer $(EXTRA_DIR)/footer.html
export COQDOCFLAGS
PUBLIC_URL="..."

_: makefile.coq

makefile.coq:
	coq_makefile -f _CoqProject -o $@

doc: makefile.coq
	rm -fr html
	COQDOCEXTRAFLAGS='--external $(PUBLIC_URL)'
	@$(MAKE) -f makefile.coq html
	cp $(EXTRA_DIR)/resources/* html

-include makefile.coq

clean::
	rm makefile.coq makefile.coq.conf
	rm -f theories/*/.*.aux theories/*/*.glob theories/*/*.vo theories/*/*.glob

.PHONY: _
