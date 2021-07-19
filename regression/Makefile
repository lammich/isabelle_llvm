ISABELLE=isabelle build -b

all: tests

isabelle:
	$(ISABELLE) -D ../thys

tests: isabelle
	$(MAKE) -C src
