
SPEC=Petr4-spec


html: ${SPEC}.mdk grammar.mdk p4.json
	madoko -vv  --odir=build $<
	
clean:
	${RM} -rf build
