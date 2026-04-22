# Makefile for building LaTeX document

# Variables
MAIN = main
LATEX = pdflatex
BIBTEX = bibtex

# Default target
all: $(MAIN).pdf

# Build PDF
$(MAIN).pdf: $(MAIN).tex sample-base.bib
	$(LATEX) $(MAIN)
	$(BIBTEX) $(MAIN)
	$(LATEX) $(MAIN)
	$(LATEX) $(MAIN)

# Clean auxiliary files
clean:
	rm -f $(MAIN).aux $(MAIN).bbl $(MAIN).blg $(MAIN).log $(MAIN).out $(MAIN).toc $(MAIN).lof $(MAIN).lot $(MAIN).fls $(MAIN).fdb_latexmk $(MAIN).synctex.gz

# Clean everything including PDF
distclean: clean
	rm -f $(MAIN).pdf

# Rebuild from scratch
rebuild: distclean all

.PHONY: all clean distclean rebuild
