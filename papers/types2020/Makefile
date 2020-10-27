main.pdf: main.tex intro.tex cultures.tex sec3.tex pbt.tex elab.tex conc.tex app.tex
	pdflatex main
	bibtex main

force:
	pdflatex main
	bibtex main

show: main.pdf
	evince main.pdf &

