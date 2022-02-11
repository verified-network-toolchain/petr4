#!/bin/bash

# set -e # Exit on error.
set -x # Make command execution verbose

mkdir /petr4/ci-test/type-checking/expectation/matched 
mkdir /petr4/ci-test/type-checking/expectation/not-matched 

#finds all p4 files in the given directory and does stuff to them
for file in $(find /petr4/ci-test/type-checking/testdata/p4_16_samples -name '*.p4' ! -name 'ipv*' ! -name 'tunneling_ubpf.p4' ! -name 'simple-actions_ubpf.p4' ! -name 'simple-firewall_ubpf.p4')
do
  # gets the result of type checking from petr4 and p4c, stores them in
  # variables and compares them
  petr4_type=$(petr4 typecheck -I /petr4/ci-test/type-checking/p4include "$file" 2>&1)
  petr4_type_stat=$?
  p4c_type=$(p4test -I /petr4/ci-test/type-checking/p4include --top4 "" "$file" 2>&1)
  p4c_type_stat=$?
  if [$petr4_type_stat eq $p4c_type_stat]
  then cp $file /petr4/ci-test/type-checking/expectation/matched
  else cp $file /petr4/ci-test/type-checking/expectation/not-matched
  fi
  # writes the file name, result of petr4 type checking, and p4c type checking
  # to a new file in res directory. 
  # echo "$file" > "/petr4/ci-test/type-checking/result/lookinto/${file##*/}.out"
  # echo "\n" >> "/petr4/ci-test/type-checking/result/lookinto/${file##*/}.out"
  # cat $file >> "/petr4/ci-test/type-checking/result/lookinto/${file##*/}.out"
  # echo "************************\n******** petr4 type checking result: ********\n************************\n" >> "/petr4/ci-test/type-checking/result/lookinto/${file##*/}.out"
  # petr4 typecheck -I /petr4/ci-test/type-checking/p4include "$file" | tee -a -i "/petr4/ci-test/type-checking/result/lookinto/${file##*/}.out"
  # echo "$petr4_type" >> "/petr4/ci-test/type-checking/result/lookinto/${file##*/}.out"
  # echo "************************\n******** p4c type checking result: ********\n************************\n" >> "/petr4/ci-test/type-checking/result/lookinto/${file##*/}.out"
  # echo "$p4c_type" >> "/petr4/ci-test/type-checking/result/lookinto/${file##*/}.out"
  # p4test -I /petr4/ci-test/type-checking/p4include --top4 "" "$file" | tee -a -i "/petr4/ci-test/type-checking/result/lookinto/${file##*/}.out"
done

