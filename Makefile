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

.PHONY: all deps build claims clean test test-stf web

all: build

build:
	dune build @install

deps:
	$(MAKE) -C deps

doc:
	dune build @doc

run:
	dune exec -- $(NAME)

install:
	dune install

claims:
	@test/claims.py

ci-test:
	dune exec -- bin/test.exe
	cd test && dune exec -- ./test.exe test -q

test-stf:
	dune exec -- bin/test.exe

test:
	cd test && dune exec -- ./test.exe

clean:
	dune clean

web:
	mkdir -p html_build/p4
	cp $(WEB_EXAMPLES) html_build/p4
	cd web && dune build ./web.bc.js --profile release && cp ../_build/default/web/web.bc.js ../html_build/ && cd ..
