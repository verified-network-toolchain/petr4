# Copyright 2019-present Cornell University
#
# Licensed under the Apache License, Version 2.0 (the "License"); you may not
# use this file except in compliance with the License. You may obtain a copy
# of the License at
#
#   http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
# WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
# License for the specific language governing permissions and limitations
# under the License.

NAME=petr4
WEB_EXAMPLES=examples/checker_tests/good/table-entries-lpm-bmv2.p4
WEB_EXAMPLES+=examples/checker_tests/good/switch_ebpf.p4
WEB_EXAMPLES+=examples/checker_tests/good/union-valid-bmv2.p4
WEB_EXAMPLES+=stf-test/custom-stf-tests/register.p4

.PHONY: all deps build claims clean test test-stf ci-test web stf-errors

all: build

build:
	dune build && echo

doc:
	dune build @doc

run: build
	dune exec -- $(NAME)

install: build
	dune install

claims: build
	@test/claims.py

ci-test: build
	dune exec -- bin/test.exe -q
	cd test && dune exec -- ./test.exe -q

test-stf: build
	dune exec -- bin/test.exe

test: build
	cd test && dune exec -- ./test.exe

clean:
	dune clean

web:
	dune build _build/default/web/web.bc.js --profile release && cp _build/default/web/web.bc.js web/html_build/

stf-errors:
	cat _build/_tests/Stf-tests/* | grep '\[failure\]' | sed 's/^ *//' | sort | uniq
