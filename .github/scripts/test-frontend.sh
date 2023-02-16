#!/usr/bin/env bash
set -e
err=0
make test
err=$?
exit ${err}
