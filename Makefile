all: practice.vo

SOURCES=$(wildcard %.v)
OBJECTS=$(patsubst %.v,%.vo,$(SOURCES))


.PHONY: all

practice.vo: Aux.vo Language.vo Maps.vo Parity.vo
	coqc practice.v

Aux.vo:
	coqc Aux.v

Language.vo:
	coqc Language.v

Maps.vo:
	coqc Maps.v

Parity.vo:
	coqc Parity.v


