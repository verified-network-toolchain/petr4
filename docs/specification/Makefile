OUTPUT=petr4 petr4-three-context styleguide
PDF_OUTPUTS=$(addsuffix .pdf,$(addprefix build/,${OUTPUT}))
HTML_OUTPUTS=$(addsuffix .html,$(addprefix build/,${OUTPUT}))
MADOKO=madoko
MADOKO_ARGS=-vv --png --odir=build

all: html

html: ${HTML_OUTPUTS} 

pdf: ${PDF_OUTPUTS}

build/%.pdf: %.mdk p4.json
	$(MADOKO) $(MADOKO_ARGS) --pdf $<

build/%.html: %.mdk p4.json
	$(MADOKO) $(MADOKO_ARGS) $<

clean:
	${RM} -rf build

.PHONY: all html pdf clean
