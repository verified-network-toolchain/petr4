#!/bin/bash

# set -e # Exit on error.
set -x # Make command execution verbose

# rm -r ci-test/type-checking/expectation/fails/*.p4*
# rm -r ci-test/type-checking/expectation/petr4TypeChecked/*.p4*
# rm -r ci-test/type-checking/expectation/typechecked/*.p4*
# rm -r ci-test/type-checking/expectation/p4cTypeChecked/*.p4*

# rm -r ci-test/type-checking/expectation/lookinto/*.p4*

# finds all p4 files in the given directory and does stuff to them
for file in $(find /petr4/ci-test/testdata/p4_16_samples -name '*.p4' ! -name 'ipv*' ! -name 'tunneling_ubpf.p4' ! -name 'simple-actions_ubpf.p4' ! -name 'simple-firewall_ubpf.p4')
do
#   # gets the result of type checking from petr4 and p4c, stores them in
#   # variables and compares them
#   file1=${file##*/}
#   file2=${file1%'.p4_out'}
#   file3="${file2}.p4"
  petr4_type=$(petr4 typecheck -I /petr4/ci-test/type-checking/p4include "$file" 2>&1)
  petr4_type_stat=$?
  p4c_type=$(p4test -I /petr4/ci-test/type-checking/p4include "$file" 2>&1)
  p4c_type_stat=$?
  if [ $petr4_type_stat = 0 ]
  then 
    if [ $p4c_type_stat = 0 ]
    then cp "$file" ci-test/type-checking/expectation/typechecked
    else cp "$file" ci-test/type-checking/expectation/petr4TypeChecked
    fi
  else 
    if [ $p4c_type_stat = 0 ]
    then cp "$file" ci-test/type-checking/expectation/p4cTypeChecked
    else cp "$file" ci-test/type-checking/expectation/fails
    fi
  fi
#   # # writes the file name, result of petr4 type checking, and p4c type checking
#   # # to a new file in res directory. 
  echo "$file" > "ci-test/type-checking/expectation/lookinto/${file##*/}_out"
  echo "\n" >> "ci-test/type-checking/expectation/lookinto/${file##*/}_out"
  cat $file >> "ci-test/type-checking/expectation/lookinto/${file##*/}_out"
  echo "************************\n******** petr4 type checking result: ********\n************************\n" >> "ci-test/type-checking/expectation/lookinto/${file##*/}_out"
  # petr4 typecheck -I /petr4/ci-test/type-checking/p4include "$file" 2>&1 | tee -a -i "ci-test/type-checking/expectation/lookinto/${file##*/}_out"
  echo "$petr4_type" >> "ci-test/type-checking/expectation/lookinto/${file##*/}_out"
  echo "************************\n******** p4c type checking result: ********\n************************\n" >> "ci-test/type-checking/expectation/lookinto/${file##*/}_out"
  echo "$p4c_type" >> "ci-test/type-checking/expectation/lookinto/${file##*/}_out"
#   # p4test -I /petr4/ci-test/type-checking/p4include "$file" 2>&1 | tee -a -i "ci-test/type-checking/expectation/lookinto/${file##*/}_out"
#   # cp "ci-test/type-checking/expectation/lookinto/${file##*/}" "ci-test/type-checking/expectation/lookinto/${file3}"
done

# moving look into files in the corresponding directory for investigation.
for file in $(find ci-test/type-checking/expectation/lookinto -name '*.p4_out')
do 
  file1=${file##*/}
  file2=${file1%'.p4_out'}
  file3="${file2}.p4"
  test -f "ci-test/type-checking/expectation/fails/${file3}" && cp -v "$file" ci-test/type-checking/expectation/fails
  test -f "ci-test/type-checking/expectation/typechecked/${file3}" && cp -v "$file" ci-test/type-checking/expectation/typechecked
  test -f "ci-test/type-checking/expectation/p4cTypeChecked/${file3}" && cp -v "$file" ci-test/type-checking/expectation/p4cTypeChecked
  test -f "ci-test/type-checking/expectation/petr4TypeChecked/${file3}" && cp -v "$file" ci-test/type-checking/expectation/petr4TypeChecked
done

