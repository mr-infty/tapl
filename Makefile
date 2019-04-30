PANDOC = pandoc
PANDOC_INCLUDES = .latex/Latex-Macros.md
PANDOC_DIRECTIVES = --variable=indent
SUBDIRS = $(wildcard */)
SOURCES = $(wildcard $(addsuffix *.md, $(SUBDIRS)))
OBJ = $(patsubst %.md, %.pdf, $(SOURCES))

all: $(OBJ)

clean:
	rm -f $(OBJ)

%.pdf: %.md
	$(PANDOC) $(PANDOC_DIRECTIVES) $(PANDOC_INCLUDES) $< -o $@
