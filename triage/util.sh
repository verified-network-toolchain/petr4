# Source this file for easy aliases for collecting and  comparing test failures.
# $ . triage/util.sh
[ -d testruns ] || mkdir testruns
alias stfnow="make test-stf 2>&1 > testruns/stfnow.txt; cat testruns/stfnow.txt | grep FAIL | sed -E 's/.* +//' | sort | uniq > testruns/stffailsnow.txt"
alias stfold="make test-stf 2>&1 > testruns/stfold.txt; cat testruns/stfold.txt | grep FAIL | sed -E 's/.* +//' | sort | uniq > testruns/stffailsold.txt"
alias chkold="make test 2>&1 | cat > testruns/testresultsold.txt; cat testruns/testresultsold.txt | grep FAIL | sed -E 's/.* +//' | sort | uniq > testruns/failsold.txt"
alias chknow="make test 2>&1 | cat > testruns/testresultsnow.txt; cat testruns/testresultsnow.txt | grep FAIL | sed -E 's/.* +//' | sort | uniq > testruns/failsnow.txt"

alias canonicalize="sort -t ',' -k1,1 -k4,4n triage/failures.csv -o triage/failures.csv"
