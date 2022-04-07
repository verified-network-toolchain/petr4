#!/bin/bash

# set -e # Exit on error.
set -x # Make command execution verbose

# mkdir ci-test/stf-test/expectation/petr4Passed
# mkdir ci-test/stf-test/expectation/passes
# mkdir ci-test/stf-test/expectation/p4cPassed
# mkdir ci-test/stf-test/expectation/fails

# mkdir ci-test/stf-test/expectation/lookinto
# echo "create dir" > ci-test/stf-test/expectation/lookinto/dummy

# rm -r ci-test/type-checking/expectation/fails/*.p4
# rm -r ci-test/type-checking/expectation/petr4TypeChecked/*.p4
# rm -r ci-test/type-checking/expectation/typechecked/*.p4
# rm -r ci-test/type-checking/expectation/p4cTypeChecked/*.p4

# rm -r ci-test/type-checking/expectation/lookinto/*
# echo "create dir" > ci-test/type-checking/expectation/lookinto/dummy

# rm -r ci-test/type-checking/expectation/lookinto/*.p4_out

# echo "directory for petr4 stf test passed but p4c didn't" > ci-test/stf-test/expectation/petr4Passed/dummy
# echo "directory for both passed" > ci-test/stf-test/expectation/passes/dummy
# echo "directory for p4c but petr4 didn't" > ci-test/stf-test/expectation/p4cPassed/dummy
# echo "directory for both failed" > ci-test/stf-test/expectation/fails/dummy

# echo "blah" | tee ci-test/type-checking/expectation/lookinto/blah.out

# finds all p4 files in the given directory and does stuff to them. 
for file in $(find /petr4/ci-test/testdata/p4_16_samples -name '*.stf')
# ! -name 'ipv*' ! -name 'tunneling_ubpf.p4' ! -name 'simple-actions_ubpf.p4' ! -name 'simple-firewall_ubpf.p4')
do
#   # gets the result of type checking from petr4 and p4c, stores them in
#   # variables and compares them
#   file1=${file##*/}
#   file2=${file1%'.p4_out'}
#   file3="${file2}.p4"
  file1="${file%.*}"
  p4_file="${file1}.p4"
  petr4_res=$(petr4 stf -I /petr4/ci-test/p4include -stf "$file" "$p4_file" 2>&1)
  # petr4_res_stat=$?
  p4c_res=$(/petr4/p4c/backends/bmv2/run-bmv2-test.py /petr4/p4c "$@" "$p4_file" 2>&1)
  # p4c_res_stat=$?
  # if [ $petr4_res_stat = 0 ]
  # then 
  #   if [ $p4c_res_stat = 0 ]
  #   then cp "$p4_file" ci-test/stf-test/expectation/passes
  #        cp "$file" ci-test/stf-test/expectation/passes
  #   else cp "$p4_file" ci-test/stf-test/expectation/petr4Passed
  #        cp "$file" ci-test/stf-test/expectation/petr4Passed
  #   fi
  # else 
  #   if [ $p4c_res_stat = 0 ]
  #   then cp "$p4_file" ci-test/stf-test/expectation/p4cPassed
  #        cp "$file" ci-test/stf-test/expectation/p4cPassed
  #   else cp "$p4_file" ci-test/stf-test/expectation/fails
  #        cp "$file" ci-test/stf-test/expectation/fails
  #   fi
  # fi
#   # # writes the file name, result of petr4 type checking, and p4c type checking
#   # # to a new file in res directory. 
  echo "p4 program:" > "ci-test/stf-test/expectation/lookinto/${file##*/}_out"
  echo "\n" >> "ci-test/stf-test/expectation/lookinto/${file##*/}_out"
  cat $p4_file >> "ci-test/stf-test/expectation/lookinto/${file##*/}_out"
  echo "\n" >> "ci-test/stf-test/expectation/lookinto/${file##*/}_out"
  echo "\n" >> "ci-test/stf-test/expectation/lookinto/${file##*/}_out"
  cat $file >> "ci-test/stf-test/expectation/lookinto/${file##*/}_out"
  echo "\n" >> "ci-test/stf-test/expectation/lookinto/${file##*/}_out"
  echo "\n" >> "ci-test/stf-test/expectation/lookinto/${file##*/}_out"
  echo "************************\n******** petr4 stf result: ********\n************************\n" >> "ci-test/stf-test/expectation/lookinto/${file##*/}_out"
  # petr4 stf -I /petr4/ci-test/p4include -stf "$file" "$p4_file" 2>&1 | tee -a -i "ci-test/stf-test/expectation/lookinto/${file##*/}_out"
  echo "$petr4_res" >> "ci-test/stf-test/expectation/lookinto/${file##*/}_out"
  echo "************************\n******** p4c stf result: ********\n************************\n" >> "ci-test/stf-test/expectation/lookinto/${file##*/}_out"
  echo "$p4c_res" >> "ci-test/stf-test/expectation/lookinto/${file##*/}_out"
  # /petr4/p4c/backends/bmv2/run-bmv2-test.py /petr4/p4c "$@" "$p4_file" 2>&1 | tee -a -i "ci-test/stf-test/expectation/lookinto/${file##*/}_out"
  # cp "ci-test/stf-test/expectation/lookinto/${file##*/}" "ci-test/stf-test/expectation/lookinto/${file3}"
done

# # # moving look into files in the corresponding directory for investigation.
# for file in $(find ci-test/type-checking/expectation/lookinto -name '*.p4_out')
# do 
#   file1=${file##*/}
#   file2=${file1%'.p4_out2'}
#   file3="${file2}.p4"
#   test -f "ci-test/type-checking/expectation/fails/${file3}" && cp -v "$file" ci-test/type-checking/expectation/fails
#   test -f "ci-test/type-checking/expectation/typechecked/${file3}" && cp -v "$file" ci-test/type-checking/expectation/typechecked
#   test -f "ci-test/type-checking/expectation/p4cTypeChecked/${file3}" && cp -v "$file" ci-test/type-checking/expectation/p4cTypeChecked
#   test -f "ci-test/type-checking/expectation/petr4TypeChecked/${file3}" && cp -v "$file" ci-test/type-checking/expectation/petr4TypeChecked
# done

# echo "dum dum" > ci-test/type-checking/expectation/lookinto/aaaaah
# cp ci-test/type-checking/expectation/lookinto/aaaaah "ci-test/type-checking/expectation/lookinto/aaaaah.out"

# rm -r ci-test/type-checking/expectation/lookinto

# once the result has been inspected we can run petr4 and p4c again 
# and compare the new files in matched and not-matched with the 
# ones in expectation.
