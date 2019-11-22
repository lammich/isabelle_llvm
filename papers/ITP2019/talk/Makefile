all: pres.pdf

# icf_struct.eps: icf_struct.dia
# 	dia -t eps -e icf_struct.eps icf_struct.dia
# 
# icf_struct.pdf: icf_struct.eps
# 	epstopdf icf_struct.eps
# 
# icf_struct.png: icf_struct.eps
# 	convert -density 300 icf_struct.eps -resize 2048x2048 icf_struct.png

pres.tex: pres.i.tex easyenum.rb
	./easyenum.rb pres.i.tex > pres.tex

pres.pdf: pres.tex *.tex #*.png
	pdflatex pres.tex && pdflatex pres.tex


%.png: %.dia
	dia -t eps -e $*.eps $*.dia
	convert -density 300 $*.eps -resize 2048x2048 $*.png
