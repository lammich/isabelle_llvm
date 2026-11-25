GEN := gen

all: pres.pdf

$(GEN):
	mkdir -p $@

$(GEN)/pres.tex: pres.i.tex easyenum.rb | $(GEN)
	./easyenum.rb pres.i.tex > $@

# latexmk tracks its own dependencies (images, inputs, reruns): always call it
pres.pdf: $(GEN)/pres.tex FORCE
	latexmk -pdf -outdir=$(GEN) -interaction=nonstopmode -halt-on-error $<
	cp -p $(GEN)/pres.pdf $@

clean:
	rm -rf $(GEN) pres.pdf

FORCE:

.PHONY: all clean FORCE
