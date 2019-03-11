
SOURCES=$(wildcard *.v)
OBJECTS=$(patsubst %.v,%.vo,$(SOURCES))
GLOBS=$(patsubst %.v,%.glob,$(SOURCES))
COQC=/usr/local/bin/coqc
COQDOC=/usr/local/bin/coqdoc
COQOPT=-R . Thesis

.PHONY: all html clean

all: $(OBJECTS)

html: $(OBJECTS) doc_dir
	$(COQDOC) -d doc/ --html $(SOURCES)

doc_dir:
	mkdir -p doc

clean: 
	rm -fr *.html *.vo *.glob doc/

Soundness.vo: Aux.vo ConcreteInterpreter.vo AbstractInterpreter.vo Soundness.v Preorder.vo
	$(COQC) $(COQOPT) Soundness.v

Parity.vo: Parity.v Aux.vo AbstractBool.vo Preorder.vo
	$(COQC) $(COQOPT) Parity.v

Preorder.vo: Preorder.v
	$(COQC) $(COQOPT) Preorder.v

ConcreteInterpreter.vo: ConcreteInterpreter.v Language.vo Maps.vo 
	$(COQC) $(COQOPT) ConcreteInterpreter.v

AbstractInterpreter.vo: AbstractInterpreter.v ConcreteInterpreter.vo Parity.vo AbstractStore.vo
	$(COQC) $(COQOPT) AbstractInterpreter.v

AbstractBool.vo: AbstractBool.v Preorder.vo
	$(COQC) $(COQOPT) AbstractBool.v

AbstractStore.vo: AbstractStore.v Parity.vo Maps.vo AbstractBool.vo
	$(COQC) $(COQOPT) AbstractStore.v

Monad.vo: Monad.v AbstractStore.vo
	$(COQC) $(COQOPT) Monad.v

%.vo : %.v
	$(COQC) $(COQOPT) $<
