#!/bin/bash

set -x # Make command execution verbose

for file in $(find /petr4/ci-test/stf-test/expectation/fails -name '*.p4')
do
  file1="${file%.*}"
  stf_file="${file1}.stf"
  echo "stf testing ${file} with petr4..."
  petr4_res=$(petr4 stf -I /petr4/ci-test/p4include -stf "$stf_file" "$file" 2>&1)
  petr4_res_stat=$?
  echo "stf testing ${file} with p4c..."
  p4c_res=$(python3 /petr4/p4c_manual/backends/bmv2/run-bmv2-test.py . -v -b -tf "$stf_file" -bd /usr/local/bin/ "$file" 2>&1)
  p4c_res_stat=$?
  if [ $petr4_type_stat != 0 -a $p4c_type_stat != 0 ]
  then echo "lable didn't match for ${file}! label was fails originally."
       err=1
  fi
done

for file in $(find /petr4/ci-test/stf-test/expectation/p4cPassed -name '*.p4')
do
    file1="${file%.*}"
    stf_file="${file1}.stf"
    echo "stf testing ${file} with petr4..."
    petr4_res=$(petr4 stf -I /petr4/ci-test/p4include -stf "$stf_file" "$file" 2>&1)
    petr4_res_stat=$?
    echo "stf testing ${file} with p4c..."
    p4c_res=$(python3 /petr4/p4c_manual/backends/bmv2/run-bmv2-test.py . -v -b -tf "$stf_file" -bd /usr/local/bin/ "$file" 2>&1)
    p4c_res_stat=$?
    if [ $petr4_type_stat != 0 -a $p4c_type_stat = 0 ]
    then echo "lable didn't match for ${file}! label was p4cPassed originally."
         err=1
    fi
done

for file in $(find /petr4/ci-test/stf-test/expectation/petr4Passed -name '*.p4')
do
    file1="${file%.*}"
    stf_file="${file1}.stf"
    echo "stf testing ${file} with petr4..."
    petr4_res=$(petr4 stf -I /petr4/ci-test/p4include -stf "$stf_file" "$file" 2>&1)
    petr4_res_stat=$?
    echo "stf testing ${file} with p4c..."
    p4c_res=$(python3 /petr4/p4c_manual/backends/bmv2/run-bmv2-test.py . -v -b -tf "$stf_file" -bd /usr/local/bin/ "$file" 2>&1)
    p4c_res_stat=$?
    if [ $petr4_type_stat = 0 -a $p4c_type_stat != 0 ]
    then echo "lable didn't match for ${file}! label was petr4Passed originally."
         err=1
    fi
done

for file in $(find /petr4/ci-test/stf-test/expectation/passes -name '*.p4')
do
    file1="${file%.*}"
    stf_file="${file1}.stf"
    echo "stf testing ${file} with petr4..."
    petr4_res=$(petr4 stf -I /petr4/ci-test/p4include -stf "$stf_file" "$file" 2>&1)
    petr4_res_stat=$?
    echo "stf testing ${file} with p4c..."
    p4c_res=$(python3 /petr4/p4c_manual/backends/bmv2/run-bmv2-test.py . -v -b -tf "$stf_file" -bd /usr/local/bin/ "$file" 2>&1)
    p4c_res_stat=$?
    if [ $petr4_type_stat = 0 -a $p4c_type_stat = 0 ]
    then echo "lable didn't match for ${file}! label was passes originally."
         err=1
    fi
done

exit ${err}

