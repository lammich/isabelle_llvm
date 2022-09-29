# ISABELLE=isabelle build -b
ISABELLE=~/opt/Isabelle2022-RC2/bin/isabelle build -b

all: tests

isabelle:
	$(ISABELLE) -D ../thys

tests: isabelle
	$(MAKE) -C src
	$(MAKE) -C aggregates
