.PHONE: all clean

TEXFILES = $(wildcard *.tex)

all: report.pdf

clean:
	@rm -f *.pdf *.dvi *.log *.aux *.fdb_latexmk *.fls

report.pdf: $(TEXFILES)
	@latexmk -pdf -pdflatex="pdflatex  -shell-escape  %O   %S" report.tex
