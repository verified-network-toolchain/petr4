P4_INCLUDE_PATH = /usr/local/share/p4c/p4include
P4C = petr4 
P4C_ARGS += typecheck -I $(P4_INCLUDE_PATH)

RUN_SCRIPT = ../../utils/run_exercise.py

ifndef TOPO
TOPO = topology.json
endif

source = $(wildcard *.p4)
compiled_json := $(source:.p4=.json)

ifndef DEFAULT_PROG
DEFAULT_PROG = $(wildcard *.p4)
endif

# Set SWITCH_EXE to override
ifdef SWITCH_EXE
run_args += -b $(SWITCH_EXE)
endif

run_args += -f $(source)
run_args += -I $(P4_INCLUDE_PATH)

all: run

run: build
	sudo PATH=$(PATH):$(HOME)/tutorials/utils python $(RUN_SCRIPT) -t $(TOPO) $(run_args)

stop:
	sudo mn -c

build:
	export PATH="$(PATH):$(HOME)/tutorials/utils" && \
	$(P4C) $(P4C_ARGS) $(source)

clean: stop
	rm -f *.pcap
	rm -rf $(BUILD_DIR) $(PCAP_DIR) $(LOG_DIR)
