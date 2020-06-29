OUTPUT=petr4 petr4-three-context styleguide
PDF_OUTPUTS=$(addsuffix .pdf,$(addprefix build/,${OUTPUT}))
HTML_OUTPUTS=$(addsuffix .html,$(addprefix build/,${OUTPUT}))

all: pdf html

pdf: ${PDF_OUTPUTS}

html: ${HTML_OUTPUTS} 

build/%.pdf: %.mdk p4.json
	madoko --pdf -vv --png --odir=build $<

build/%.html: %.mdk p4.json
	madoko -vv --png --odir=build $<

clean:
	${RM} -rf build

.PHONY: all html pdf clean
