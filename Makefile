
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

practice.vo: Aux.vo ConcreteInterpreter.vo AbstractInterpreter.vo 
	coqc practice.v

Parity.vo: Parity.v Aux.vo 
	coqc Parity.v

ConcreteInterpreter.vo: ConcreteInterpreter.v Language.vo Maps.vo 
	coqc ConcreteInterpreter.v

AbstractInterpreter.vo: AbstractInterpreter.v Language.vo Maps.vo Parity.vo
	coqc AbstractInterpreter.v

AbstractBool.vo: AbstractBool.v
	coqc AbstractBool.v

AbstractState.vo: AbstractState.v Parity.vo Maps.vo
	coqc AbstractState.v

%.vo : %.v
	coqc $<
