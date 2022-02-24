#!/bin/bash

# set -e # Exit on error.
set -x # Make command execution verbose


# mkdir ci-test/type-checking/expectation/petr4TypeChecked
# mkdir ci-test/type-checking/expectation/typechecked
# mkdir ci-test/type-checking/expectation/p4cTypeChecked
# mkdir ci-test/type-checking/expectation/fails

# mkdir ci-test/type-checking/expectation/lookinto
# echo "create dir" > ci-test/type-checking/expectation/lookinto/dummy

# rm -r ci-test/type-checking/expectation/fails/*.p4
# rm -r ci-test/type-checking/expectation/petr4TypeChecked/*.p4
# rm -r ci-test/type-checking/expectation/typechecked/*.p4
# rm -r ci-test/type-checking/expectation/p4cTypeChecked/*.p4


# echo "directory for petr4 typechecked but p4c didn't" > ci-test/type-checking/expectation/petr4TypeChecked/dummy
# echo "directory for both typechecked" > ci-test/type-checking/expectation/typechecked/dummy
# echo "directory for p4c typechecked but petr4 didn't" > ci-test/type-checking/expectation/p4cTypeChecked/dummy
# echo "directory for both failed" > ci-test/type-checking/expectation/fails/dummy

# finds all p4 files in the given directory and does stuff to them
for file in $(find /petr4/ci-test/type-checking/testdata/p4_16_samples -name '*.p4' ! -name 'ipv*' ! -name 'tunneling_ubpf.p4' ! -name 'simple-actions_ubpf.p4' ! -name 'simple-firewall_ubpf.p4')
do
  # gets the result of type checking from petr4 and p4c, stores them in
  # variables and compares them
  file1=${file##*/}
  file2=${file1%'.p4'}
  file3="${file2}.out"
  petr4_type=$(petr4 typecheck -I /petr4/ci-test/type-checking/p4include "$file")
  petr4_type_stat=$?
  p4c_type=$(p4test -I /petr4/ci-test/type-checking/p4include "$file")
  # 2>&1
  p4c_type_stat=$?
  # if [ $petr4_type_stat = 0 ]
  # then 
  #   if [ $p4c_type_stat = 0 ]
  #   then cp "$file" ci-test/type-checking/expectation/typechecked
  #   else cp "$file" ci-test/type-checking/expectation/petr4TypeChecked
  #   fi
  # else 
  #   if [ $p4c_type_stat = 0 ]
  #   then cp "$file" ci-test/type-checking/expectation/p4cTypeChecked
  #   else cp "$file" ci-test/type-checking/expectation/fails
  #   fi
  # fi
  # # writes the file name, result of petr4 type checking, and p4c type checking
  # # to a new file in res directory. 
  echo "$file" > "ci-test/type-checking/expectation/lookinto/${file1}"
  echo "\n" >> "ci-test/type-checking/expectation/lookinto/${file1}"
  cat $file >> "ci-test/type-checking/expectation/lookinto/${file1}"
  echo "************************\n******** petr4 type checking result: ********\n************************\n" >> "ci-test/type-checking/expectation/lookinto/${file1}"
  petr4 typecheck -I /petr4/ci-test/type-checking/p4include "$file" | tee -a -i "ci-test/type-checking/expectation/lookinto/${file1}"
  # echo "$petr4_type" >> "ci-test/type-checking/expectation/lookinto/${file3}"
  echo "************************\n******** p4c type checking result: ********\n************************\n" >> "ci-test/type-checking/expectation/lookinto/${file1}"
  # echo "$p4c_type" >> "ci-test/type-checking/expectation/lookinto/${file3}"
  p4test -I /petr4/ci-test/type-checking/p4include "$file" | tee -a -i "ci-test/type-checking/expectation/lookinto/${file1}"
  mv "ci-test/type-checking/expectation/lookinto/${file1}" "ci-test/type-checking/expectation/lookinto/${file3}"
done

# # # moving look into files in the corresponding directory for investigation.
# for file in $(find ci-test/type-checking/expectation/lookinto -name '*.out')
# do 
#   file1=${file##*/}
#   file2=${file1%'.out'}
#   file3="${file2}.p4"
#   test -f "ci-test/type-checking/expectation/fails/${file3}" && cp "$file" ci-test/type-checking/expectation/fails
#   test -f "ci-test/type-checking/expectation/typechecked/${file3}" && cp "$file" ci-test/type-checking/expectation/typechecked
#   test -f "ci-test/type-checking/expectation/p4cTypeChecked/${file3}" && cp "$file" ci-test/type-checking/expectation/p4cTypeChecked
#   test -f "ci-test/type-checking/expectation/petr4TypeChecked/${file3}" && cp "$file" ci-test/type-checking/expectation/petr4TypeChecked
# done

# rm -r ci-test/type-checking/expectation/lookinto

# once the result has been inspected we can run petr4 and p4c again 
# and compare the new files in matched and not-matched with the 
# ones in expectation.