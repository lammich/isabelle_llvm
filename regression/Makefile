# ISABELLE=isabelle build -b



ISABELLE ?= "isabelle"

all: tests

isabelle:
	$(ISABELLE) build -b -D ../thys

tests: isabelle
	$(MAKE) -C src
	$(MAKE) -C aggregates
