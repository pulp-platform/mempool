TARGETS := $(patsubst %.fods,%.pdf,$(wildcard *.fods))

all: ${TARGETS}

%.pdf: %.fods
	$(if $(shell pgrep soffice), $(error Close all running LibreOffice instances before making!))
	soffice --convert-to pdf $< --headless

.PHONY: clean
clean:
	rm -f *.pdf
