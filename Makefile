EXTRA_DIR:= doc-config
COQDOCFLAGS:= \
  --external 'http://ssr2.msr-inria.inria.fr/doc/ssreflect-1.5/' Ssreflect \
  --external 'http://ssr2.msr-inria.inria.fr/doc/mathcomp-1.5/' MathComp \
  --toc --toc-depth 2 --html --interpolate \
  --index indexpage --no-lib-name --parse-comments \
  --with-header $(EXTRA_DIR)/header.html --with-footer $(EXTRA_DIR)/footer.html
export COQDOCFLAGS

_: makefile.coq

makefile.coq: _CoqProject
	coq_makefile $(shell cat _CoqProject) _build/default/theories/iSL/*.v > $@ 2> /dev/null

all: duneall

duneall:
	dune build --display short

doc: makefile.coq
	rm -fr html
	COQDOCEXTRAFLAGS='--external "https://ipq.gitlab.io/doc/"'
	@$(MAKE) -f makefile.coq html
	cp $(EXTRA_DIR)/resources/* html

-include makefile.coq

clean::
	rm makefile.coq
	dune clean
	rm -f theories/.*.aux theories/*.glob theories/*.vo theories/*.glob

demo: _build/default/bin/propquant.exe
	_build/default/bin/propquant.exe $()

release:
	tar -zcvf release.tar.gz Makefile theories/*.v bin/ extraction _CoqProject  dune dune-project theories/dune README.md

.PHONY: _
