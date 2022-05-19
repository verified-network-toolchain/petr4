#!/bin/bash

# set -e # Exit on error.
# set -x # Make command execution verbose

err=0
# reminder: testdata and p4include have been moved to ci-test.



# finds all p4 files in the given directory and does stuff to them
for file in $(find /petr4/ci-test/type-checking/expectation/fails -name '*.p4')
do
  # gets the result of type checking from petr4 and p4c, stores them in
  # variables and compares them
  # file1=${file##*/}
  # file2=${file1%'.p4_out'}
  # file3="${file2}.p4"
  echo "type checking ${file} with petr4"
  petr4_type=$(petr4 typecheck -I /petr4/ci-test/type-checking/p4include "$file" 2>&1)
  petr4_type_stat=$?
  echo "type checking ${file} with p4c"
  p4c_type=$(p4test -I /petr4/ci-test/type-checking/p4include "$file" 2>&1)
  p4c_type_stat=$?
  if [ $petr4_type_stat != 0 && $p4c_type_stat != 0 ]
  then echo "lable didn't mismatch for ${file}! label was fails originally."
       err=1
  fi
done

exit ${err}

#   # if [ $petr4_type_stat = 0 ]
#   # then 
#   #   if [ $p4c_type_stat = 0 ]
#   #   then cp "$file" ci-test/type-checking/expectation/typechecked
#   #   else cp "$file" ci-test/type-checking/expectation/petr4TypeChecked
#   #   fi
#   # else 
#   #   if [ $p4c_type_stat = 0 ]
#   #   then cp "$file" ci-test/type-checking/expectation/p4cTypeChecked
#   #   else cp "$file" ci-test/type-checking/expectation/fails
#   #   fi
#   # fi
#   # # writes the file name, result of petr4 type checking, and p4c type checking
#   # # to a new file in res directory. 
#   echo "$file" > "ci-test/type-checking/expectation/lookinto/${file##*/}_out2"
#   echo "\n" >> "ci-test/type-checking/expectation/lookinto/${file##*/}_out2"
#   cat $file >> "ci-test/type-checking/expectation/lookinto/${file##*/}_out2"
#   echo "************************\n******** petr4 type checking result: ********\n************************\n" >> "ci-test/type-checking/expectation/lookinto/${file##*/}_out2"
#   # petr4 typecheck -I /petr4/ci-test/type-checking/p4include "$file" 2>&1 | tee -a -i "ci-test/type-checking/expectation/lookinto/${file##*/}_out"
#   echo "$petr4_type" >> "ci-test/type-checking/expectation/lookinto/${file##*/}_out2"
#   echo "************************\n******** p4c type checking result: ********\n************************\n" >> "ci-test/type-checking/expectation/lookinto/${file##*/}_out2"
#   echo "$p4c_type" >> "ci-test/type-checking/expectation/lookinto/${file##*/}_out2"
#   # p4test -I /petr4/ci-test/type-checking/p4include "$file" 2>&1 | tee -a -i "ci-test/type-checking/expectation/lookinto/${file##*/}_out"
#   # cp "ci-test/type-checking/expectation/lookinto/${file##*/}" "ci-test/type-checking/expectation/lookinto/${file3}"
# done

# # # moving look into files in the corresponding directory for investigation.
# for file in $(find ci-test/type-checking/expectation/lookinto -name '*.p4_out2')
# do 
#   file1=${file##*/}
#   file2=${file1%'.p4_out2'}
#   file3="${file2}.p4"
#   test -f "ci-test/type-checking/expectation/fails/${file3}" && cp -v "$file" ci-test/type-checking/expectation/fails
#   test -f "ci-test/type-checking/expectation/typechecked/${file3}" && cp -v "$file" ci-test/type-checking/expectation/typechecked
#   test -f "ci-test/type-checking/expectation/p4cTypeChecked/${file3}" && cp -v "$file" ci-test/type-checking/expectation/p4cTypeChecked
#   test -f "ci-test/type-checking/expectation/petr4TypeChecked/${file3}" && cp -v "$file" ci-test/type-checking/expectation/petr4TypeChecked
# done



