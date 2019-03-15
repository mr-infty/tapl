PANDOC_INCLUDES = ./Latex-Macros.md
SUBDIRS = $(wildcard */)
SOURCES = $(wildcard $(addsuffix *.md, $(SUBDIRS)))
OBJ = $(patsubst %.md, %.pdf, $(SOURCES))

all: $(OBJ)

clean:
	rm -f $(OBJ)

%.pdf: %.md
	pandoc $(PANDOC_INCLUDES) $< -o $@
