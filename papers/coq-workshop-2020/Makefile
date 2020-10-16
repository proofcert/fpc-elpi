main.pdf: main.tex macros.tex
	pdflatex main
	bibtex main

show: main.pdf
	evince main.pdf &

bib: 
	bibtex main

force:
	pdflatex main
	bibtex main

dropbox: main.pdf
	cp main.pdf    ~/Dropbox/Sync/Drafts/coq-workshop-2020.pdf

publish: main.pdf
	cp main.pdf ~/www/papers/coq-workshop-2020.pdf

export.bib: main.tex
	bibexport -o export.bib main.aux
