paper.pdf: paper.tex ../ijcar2020/macros.tex
	pdflatex paper
#	bibtex paper

show: paper.pdf
	evince paper.pdf &

bib: 
	bibtex paper

force:
	pdflatex paper
#	bibtex paper

dropbox: paper.pdf
	cp paper.pdf    ~/Dropbox/Sync/Drafts/lfmtp2020.pdf

publish: paper.pdf
	cp paper.pdf ~/www/papers/elpi-coq.pdf

export.bib: paper.tex
	bibexport -o export.bib paper.aux

clean:
	rm paper.aux paper.bbl paper.blg paper.log paper.out paper.pag paper.pdf

zip: paper.tex
	zip project.zip paper.tex eptcs.bst eptcs.cls

