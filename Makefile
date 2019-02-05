all: practice.vo

SOURCES=$(wildcard *.v)
OBJECTS=$(patsubst %.v,%.vo,$(SOURCES))
GLOBS=$(patsubst %.v,%.glob,$(SOURCES))

.PHONY: all html clean

html: $(OBJECTS) doc_dir
	coqdoc -d doc/ --html $(SOURCES)

doc_dir:
	mkdir -p doc

clean: 
	rm -f *.html *.vo *.glob

practice.vo: Aux.vo ConcreteInterpreter.vo AbstractInterpreter.vo 
	coqc practice.v

Aux.vo: Aux.v 
	coqc Aux.v

Language.vo: Language.v 
	coqc Language.v

Maps.vo: Maps.v 
	coqc Maps.v

Parity.vo: Parity.v Aux.vo 
	coqc Parity.v

ConcreteInterpreter.vo: ConcreteInterpreter.v Language.vo Maps.vo 
	coqc ConcreteInterpreter.v

AbstractInterpreter.vo: AbstractInterpreter.v Language.vo Maps.vo Parity.vo
	coqc AbstractInterpreter.v
