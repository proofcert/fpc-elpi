paper.pdf: paper.tex macros.tex
	pdflatex paper
	bibtex paper

show: paper.pdf
	evince paper.pdf &

bib: 
	bibtex paper

force:
	pdflatex paper
	bibtex paper

dropbox: paper.pdf
	cp paper.pdf    ~/Dropbox/Sync/Drafts/ijcar2020.pdf

publish: paper.pdf
	cp paper.pdf ~/www/papers/lppt-extended.pdf

export.bib: paper.tex
	bibexport -o export.bib paper.aux
