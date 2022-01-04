#!/bin/bash

set -e  # Exit on error.
set -x  # Make command execution verbose


# get testdata from p4c git
mkdir p4cgit
cd p4cgit
git clone https://github.com/p4lang/p4c.git


# typecheck all tests with petr4 and write results
# petr4 typecheck -I <path to core and etc> <p4 file with full path>
# p4test -I <path to core and etc> --top4 "" <p4 file with full path>
# for file in </p4cgit/p4c/testdata/*>
# do 
#   command ... "$file" 
# done

# find /p4cgit/p4c/testdata/ -type p4 -exec command {options} {} \; > results.out
find /petr4/p4cgit/p4c/testdata/ -name "*.p4" -exec petr4 typecheck -I /petr4/p4cgit/p4c/p4include/ {} \; > /petr4/results/petr4-results.out \; -exec p4test -I /petr4/p4cgit/p4c/p4include/ --top4 "" {} \; > /petr4/results/p4c-results.out






