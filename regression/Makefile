ISABELLE=~/opt/Isabelle2021-1-RC3/bin/isabelle build -b

all: tests

isabelle:
	$(ISABELLE) -D ../thys

tests: isabelle
	$(MAKE) -C src
