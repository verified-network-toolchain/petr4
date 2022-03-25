#!/usr/bin/env bash

# directory for programs we EXpect to PASS
EXPASS="./examples/compile_tests"
INCLUDE="./examples"

err=0

INCLUDE_DIR="examples"

PETR4="petr4 compile -I ${INCLUDE} -gcl 1000 -gcl 10"

for TEST_FILE in ${EXPASS}/*; do
    echo "testing ${TEST_FILE}"
    ${PETR4} ${TEST_FILE} > /dev/null
    code=$?; (( err |= ${code} ))
    if [ ${code} -eq 0 ]; then
        echo "PASS"
    else
        echo "FAIL"
    fi
done

exit ${err}
