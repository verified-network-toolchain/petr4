
SPEC=Petr4-spec

all: build/${SPEC}.pdf

build/${SPEC}.pdf: ${SPEC}.mdk
	madoko --pdf -vv --odir=build $<

build/${SPEC}.pdf: grammar.mdk p4.json

html: ${SPEC}.mdk grammar.mdk p4.json
	madoko -vv  --odir=build $<
	
clean:
	${RM} -rf build
