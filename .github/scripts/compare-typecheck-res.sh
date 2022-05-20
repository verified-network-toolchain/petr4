#!/bin/bash

# set -x # Make command execution verbose

err=0

for file in $(find /petr4/ci-test/type-checking/expectation/fails -name '*.p4' ! -name 'next.p4' ! -name 'filtering.p4' ! -name 'forwarding.p4' ! -name 'int_header.p4' ! name 'acl.p4')
do
  petr4_type=$(petr4 typecheck -I /petr4/ci-test/p4include "$file" 2>&1)
  petr4_type_stat=$?
  p4c_type=$(p4test -I /petr4/ci-test/p4include "$file" 2>&1)
  p4c_type_stat=$?
  if [ $petr4_type_stat != 0 -a $p4c_type_stat != 0 ]
  then echo "${file} PASSED!"
  else echo "type checking ${file} with petr4 resulted in ${petr4_typ_stat}"
       echo "type checking ${file} with p4c resulted in ${p4c_typ_stat}"
       echo "lable didn't match for ${file}! label was fails originally."
       err=1
  fi
done

for file in $(find /petr4/ci-test/type-checking/expectation/p4cTypeChecked -name '*.p4')
do
    petr4_type=$(petr4 typecheck -I /petr4/ci-test/p4include "$file" 2>&1)
    petr4_type_stat=$?
    p4c_type=$(p4test -I /petr4/ci-test/p4include "$file" 2>&1)
    p4c_type_stat=$?
    if [ $petr4_type_stat != 0 -a $p4c_type_stat = 0 ]
    then echo "${file} PASSED!"
    else echo "type checking ${file} with petr4 resulted in ${petr4_typ_stat}"
         echo "type checking ${file} with p4c resulted in ${p4c_typ_stat}"
         echo "lable didn't match for ${file}! label was p4cTypeChecked originally."
         err=1
    fi
done

for file in $(find /petr4/ci-test/type-checking/expectation/petr4TypeChecked -name '*.p4')
do
    petr4_type=$(petr4 typecheck -I /petr4/ci-test/p4include "$file" 2>&1)
    petr4_type_stat=$?
    p4c_type=$(p4test -I /petr4/ci-test/p4include "$file" 2>&1)
    p4c_type_stat=$?
    if [ $petr4_type_stat = 0 -a $p4c_type_stat != 0 ]
    then echo "${file} PASSED!"
    else echo "type checking ${file} with petr4 resulted in ${petr4_typ_stat}"
         echo "type checking ${file} with p4c resulted in ${p4c_typ_stat}"
         echo "lable didn't match for ${file}! label was petr4TypeChecked originally."
         err=1
    fi
done

for file in $(find /petr4/ci-test/type-checking/expectation/typechecked -name '*.p4')
do
    petr4_type=$(petr4 typecheck -I /petr4/ci-test/p4include "$file" 2>&1)
    petr4_type_stat=$?
    p4c_type=$(p4test -I /petr4/ci-test/p4include "$file" 2>&1)
    p4c_type_stat=$?
    if [ $petr4_type_stat = 0 -a $p4c_type_stat = 0 ]
    then echo "${file} PASSED!"
    else echo "type checking ${file} with petr4 resulted in ${petr4_typ_stat}"
         echo "type checking ${file} with p4c resulted in ${p4c_typ_stat}"
         echo "lable didn't match for ${file}! label was typechecked originally."
         err=1
    fi
done

exit ${err}




