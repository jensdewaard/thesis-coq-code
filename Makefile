all: practice.vo

SOURCES=$(wildcard %.v)
OBJECTS=$(patsubst %.v,%.vo,$(SOURCES))


.PHONY: all

practice.vo: Aux.vo Language.vo Maps.vo Parity.vo
	coqc practice.v

Aux.vo: Aux.v
	coqc Aux.v

Language.vo: Language.v
	coqc Language.v

Maps.vo: Maps.v
	coqc Maps.v

Parity.vo: Parity.v
	coqc Parity.v


