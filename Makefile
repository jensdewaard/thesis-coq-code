
SOURCES=$(wildcard *.v)
OBJECTS=$(patsubst %.v,%.vo,$(SOURCES))
GLOBS=$(patsubst %.v,%.glob,$(SOURCES))

.PHONY: all html clean

all: $(OBJECTS)

html: $(OBJECTS) doc_dir
	coqdoc -d doc/ --html $(SOURCES)

doc_dir:
	mkdir -p doc

clean: 
	rm -fr *.html *.vo *.glob doc/

Soundness.vo: Aux.vo ConcreteInterpreter.vo AbstractInterpreter.vo Soundness.v
	coqc Soundness.v

Parity.vo: Parity.v Aux.vo 
	coqc Parity.v

ConcreteInterpreter.vo: ConcreteInterpreter.v Language.vo Maps.vo 
	coqc ConcreteInterpreter.v

AbstractInterpreter.vo: AbstractInterpreter.v ConcreteInterpreter.vo Parity.vo AbstractStore.vo
	coqc AbstractInterpreter.v

AbstractBool.vo: AbstractBool.v
	coqc AbstractBool.v

AbstractStore.vo: AbstractStore.v Parity.vo Maps.vo
	coqc AbstractStore.v

%.vo : %.v
	coqc $<
