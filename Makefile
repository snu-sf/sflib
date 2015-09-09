VS           := $(wildcard *.v)
IS           := $(sort $(subst /, , $(dir $(VS))))
COQLIBS      := $(addprefix -I ,$(IS))
MAKECOQ=$(MAKE) -f Makefile.coq COQLIBS="$(COQLIBS)"
DOC          := doc

.PHONY: all theories doc clean

all: theories

Makefile.coq: Makefile $(VS)
	coq_makefile $(VS) -o Makefile.coq

theories: Makefile.coq
	+$(MAKECOQ)

doc: theories
	mkdir -p $(DOC)
	coqdoc $(VS) -d $(DOC)

clean:
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq
