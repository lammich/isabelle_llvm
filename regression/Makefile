ISABELLE=~/opt/Isabelle2021-1/bin/isabelle build -b

all: tests

isabelle:
	$(ISABELLE) -D ../thys

tests: isabelle
	$(MAKE) -C src
