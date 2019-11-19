
OUTPUT=petr4

all: build/${OUTPUT}.pdf

build/${OUTPUT}.pdf: ${OUTPUT}.mdk p4.json
	madoko --pdf -vv --png --odir=build $<

html: ${OUTPUT}.mdk p4.json
	madoko -vv --png --odir=build $<

clean:
	${RM} -rf build
