all: practice.vo

SOURCES=$(wildcard %.v)
OBJECTS=$(patsubst %.v,%.vo,$(SOURCES))


.PHONY: all

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

ConcreteInterpreter.vo: ConcreteInterpreter.v Language.vo
	coqc ConcreteInterpreter.v

AbstractInterpreter.vo: AbstractInterpreter.v Language.vo
	coqc AbstractInterpreter.v
