petr4 compile -I ./examples $1  -printp4cub -export-file ./deps/poulet4_Ccomp/compiled.c -gen-loc -normalize
 gcc -o ./ctest.o deps/poulet4_Ccomp/V1model.c -lgmp -lm 
 ./ctest.o $2 1
 