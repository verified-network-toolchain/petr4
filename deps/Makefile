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

.PHONY: all poulet4 poulet4_Ccomp

all: poulet4 poulet4_Ccomp

poulet4:
	opam unpin poulet4 --yes
	$(MAKE) -C ./poulet4
	opam install ./poulet4 --working-dir --yes

poulet4_Ccomp: poulet4
	$(MAKE) -C poulet4_Ccomp clean
	$(MAKE) -C poulet4_Ccomp
	opam unpin poulet4_Ccomp --yes
	opam install ./poulet4_Ccomp/extraction --working-dir --yes

clean:
	$(MAKE) -C poulet4 clean
	$(MAKE) -C poulet4_Ccomp clean
