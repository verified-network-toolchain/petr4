#!/bin/bash

# set -x # Make command execution verbose

for file in $(find /petr4/ci-test/stf-test/expectation/fails -name '*.p4')
do
  file1="${file%.*}"
  stf_file="${file1}.stf"
  petr4_res=$(petr4 stf -I /petr4/ci-test/p4include -stf "$stf_file" "$file" 2>&1)
  petr4_res_stat=$?
  p4c_res=$(python3 /petr4/p4c_manual/backends/bmv2/run-bmv2-test.py . -v -b -tf "$stf_file" -bd /usr/local/bin/ "$file" 2>&1)
  p4c_res_stat=$?
  if [ $petr4_res_stat != 0 -a $p4c_res_stat != 0 ]
  then echo "${file} PASSED!"
  else echo "type checking ${file} with petr4 resulted in ${petr4_res_stat}"
       echo "type checking ${file} with p4c resulted in ${p4c_res_stat}"
       echo "lable didn't match for ${file}! label was fails originally."
       err=1
  fi
done

for file in $(find /petr4/ci-test/stf-test/expectation/p4cPassed -name '*.p4' ! -name 'ipv6-switch-ml-bmv2.p4' ! -name 'count_ebpf.p4' ! -name 'valid_ebpf.p4')
do
    file1="${file%.*}"
    stf_file="${file1}.stf"
    petr4_res=$(petr4 stf -I /petr4/ci-test/p4include -stf "$stf_file" "$file" 2>&1)
    petr4_res_stat=$?
    p4c_res=$(python3 /petr4/p4c_manual/backends/bmv2/run-bmv2-test.py . -v -b -tf "$stf_file" -bd /usr/local/bin/ "$file" 2>&1)
    p4c_res_stat=$?
    if [ $petr4_res_stat != 0 -a $p4c_res_stat = 0 ]
    then echo "${file} PASSED!"
    else echo "type checking ${file} with petr4 resulted in ${petr4_res_stat}"
         echo "type checking ${file} with p4c resulted in ${p4c_res_stat}"
         echo "lable didn't match for ${file}! label was p4cPassed originally."
         err=1
    fi
done

for file in $(find /petr4/ci-test/stf-test/expectation/petr4Passed -name '*.p4')
do
    file1="${file%.*}"
    stf_file="${file1}.stf"
    petr4_res=$(petr4 stf -I /petr4/ci-test/p4include -stf "$stf_file" "$file" 2>&1)
    petr4_res_stat=$?
    p4c_res=$(python3 /petr4/p4c_manual/backends/bmv2/run-bmv2-test.py . -v -b -tf "$stf_file" -bd /usr/local/bin/ "$file" 2>&1)
    p4c_res_stat=$?
    if [ $petr4_res_stat = 0 -a $p4c_res_stat != 0 ]
    then echo "${file} PASSED!"
    else echo "type checking ${file} with petr4 resulted in ${petr4_res_stat}"
         echo "type checking ${file} with p4c resulted in ${p4c_res_stat}"
         echo "lable didn't match for ${file}! label was petr4Passed originally."
         err=1
    fi
done

for file in $(find /petr4/ci-test/stf-test/expectation/passes -name '*.p4' ! -name 'arith5-bmv2.p4' ! -name 'default_action-bmv2.p4' ! -name 'arith-bmv2.p4' ! -name 'constant-in-calculation-bmv2.p4' ! -name 'arith1-bmv2.p4' ! -name 'arith-inline-bmv2.p4' ! -name 'enum-bmv2.p4' ! -name 'arith2-bmv2.p4' ! -name 'arith2-inline-bmv2.p4' ! -name 'key-bmv2.p4' ! -name 'arith3-bmv2.p4' ! -name 'arith4-bmv2.p4')
do
    file1="${file%.*}"
    stf_file="${file1}.stf"
    petr4_res=$(petr4 stf -I /petr4/ci-test/p4include -stf "$stf_file" "$file" 2>&1)
    petr4_res_stat=$?
    p4c_res=$(python3 /petr4/p4c_manual/backends/bmv2/run-bmv2-test.py . -v -b -tf "$stf_file" -bd /usr/local/bin/ "$file" 2>&1)
    p4c_res_stat=$?
    if [ $petr4_res_stat = 0 -a $p4c_res_stat = 0 ]
    then echo "${file} PASSED!"
    else echo "type checking ${file} with petr4 resulted in ${petr4_res_stat}"
         echo "type checking ${file} with p4c resulted in ${p4c_res_stat}"
         echo "lable didn't match for ${file}! label was passes originally."
         err=1
    fi
done

exit ${err}

