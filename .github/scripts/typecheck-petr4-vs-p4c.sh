#!/bin/bash

set -e # Exit on error.
set -x # Make command execution verbose

# typecheck all tests with petr4 and write results
# petr4 typecheck -I <path to core and etc> <p4 file with full path>
# p4test -I <path to core and etc> --top4 "" <p4 file with full path>
# for file in /petr4/p4cgit/p4c/testdata/
# do
#   petr4 typecheck -I /petr4/p4cgit/p4c/p4include/ "$file" > "/petr4/results/petr4-results/${file%*}.out"
#   p4test -I /petr4/p4cgit/p4c/p4include/ --top4 "" "$file" > "/petr4/results/p4c-results/${file%*}.out"
# done

# # find /p4cgit/p4c/testdata/ -type p4 -exec command {options} {} \; > results.out

# find /petr4/p4cgit/p4c/testdata/ -name "*.p4" -exec petr4 typecheck -I /petr4/p4cgit/p4c/p4include/ ${0} \; > /petr4/results/petr4-results/${0}.out

# find /petr4/p4cgit/p4c/testdata/ -exec p4test -I /petr4/p4cgit/p4c/p4include/ --top4 "" {} \; > /petr4/results/p4c-results.out

# find /petr4/examples/checker_tests/excluded -name "*.p4" -exec petr4 typecheck -I /petr4/examples {} \; -exec p4test -I /petr4/examples --top4 "" {} \; > /petr4/results/p4c-results.out

# find /petr4/examples/checker_tests/good/ -name "*.p4" | xargs -t petr4 typecheck -I /petr4/examples/


#finds all p4 files in the given directory and does stuff to them
for file in $(find /petr4/ci-test/type-checking/testdata/p4_16_samples -name '*.p4' ! -name 'ipv*' ! -name 'tunneling_ubpf.p4')
do
  # gets the result of type checking from petr4 and p4c, stores them in
  # variables and compares them
  # petr4_type=$(petr4 typecheck -I /petr4/ci-test/type-checking/p4include "$file" 2>&1)
  # p4c_type=$(p4test -I /petr4/ci-test/type-checking/p4include --top4 "" "$file" 2>&1)
  # writes the file name, result of petr4 type checking, and p4c type checking
  # to a new file in res directory. 
  echo "$file" > "/petr4/ci-test/type-checking/result/lookinto/${file##*/}.out"
  echo "\n" >> "/petr4/ci-test/type-checking/result/lookinto/${file##*/}.out"
  cat $file >> "/petr4/ci-test/type-checking/result/lookinto/${file##*/}.out"
  echo "************************\n******** petr4 type checking result: ********\n************************\n" >> "/petr4/ci-test/type-checking/result/lookinto/${file##*/}.out"
  petr4 typecheck -I /petr4/ci-test/type-checking/p4include "$file" | tee -a -i "/petr4/ci-test/type-checking/result/lookinto/${file##*/}.out"
  echo "$petr4_type" >> "/petr4/ci-test/type-checking/result/lookinto/${file##*/}.out"
  echo "************************\n******** p4c type checking result: ********\n************************\n" >> "/petr4/ci-test/type-checking/result/lookinto/${file##*/}.out"
  # echo "$p4c_type" >> "/petr4/ci-test/type-checking/result/lookinto/${file##*/}.out"
  p4test -I /petr4/ci-test/type-checking/p4include --top4 "" "$file" | tee -a -i "/petr4/ci-test/type-checking/result/lookinto/${file##*/}.out"
  #TODO: add the following later!
#   # creates the expectation dir. 
#   if [ $petr4_type == $p4c_type ]
#   then 
#     cp $file /petr4/ci-test/type-checking/expectation/matched
#   else 
#   	cp $file /petr4/ci-test/type-checking/expectation/not-matched
#   fi
#   # locates files in mathced or not-matched folders.
#   if [ $petr4_type == $p4c_type ]
#   then 
#     cp $file /petr4/ci-test/type-checking/result/matched
#   else 
#   	cp $file /petr4/ci-test/type-checking/result/not-matched
#   fi
done
# # compares result and expection 
# expec_match_minus_res_match = $(find "$/petr4/ci-test/type-checking/expectation/matched/" "$/petr4/ci-test/type-checking/result/matched/" "$/petr4/ci-test/type-checking/result/matched/" -printf '%P\n' | sort | uniq -u)
# expec_notmatch_minus_res_match = $(find "$/petr4/ci-test/type-checking/expectation/not-matched/" "$/petr4/ci-test/type-checking/result/not-matched/" "$/petr4/ci-test/type-checking/result/not-matched/" -printf '%P\n' | sort | uniq -u)
# echo "match is: \n" 
# echo "$expec_match_minus_res_match"
# echo "not-matched is: \n"
# echo "$expec_notmatch_minus_res_match"
# if [[ -n $expec_match_minus_res_match ]]
# then 
#   echo "matched expectation - result is not empty. here are the troublesome files: \n" 
#   echo "$expec_match_minus_res_match"
#   exit 1
# else 
#   if [[ -n $expec_notmatch_minus_res_match ]]
#   then 
#     echo "not-matched expectation - result is not empty. here are the troublesome files: \n" 
#     echo "$expec_notmatch_minus_res_match"
#     exit 1
#   else 
#     echo "EVERYTHING CHECKED OUT! YOOHOO!"
#   fi
# fi

# #find "$/examples/checker_tests/bad/" "$/examples/checker_tests/good/" "$/examples/checker_tests/good/" -printf '%P\n' | sort | uniq -u

