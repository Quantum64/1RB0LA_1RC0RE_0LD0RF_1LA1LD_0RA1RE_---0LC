COQC ?= coqc
COQCHK ?= coqchk
COQCHKFLAGS ?= -silent -bytecode-compiler yes
COQDEP ?= coqdep
COQTOP ?= coqtop
FLAGS = -Q ../../../busycoq/verify BusyCoq -Q ../../../busycoq/verify/BigInt BigInt -Q . MinimalSim

SOURCES = Machine.v Derivation.v Simulator.v Reflection.v Theorem.v

.PHONY: all audit fresh clean
all: Theorem.vo

%.vo: %.v
	$(COQC) $(FLAGS) $<

.coqdeps: Makefile $(SOURCES)
	@$(COQDEP) $(FLAGS) $(SOURCES) > $@

ifneq ($(filter clean,$(MAKECMDGOALS)),clean)
-include .coqdeps
endif

audit: all
	@audit_dir=$$(mktemp -d /tmp/tm-coq-audit.XXXXXX); \
	trap 'rm -rf "$$audit_dir"' EXIT HUP INT TERM; \
	printf '%s\n' \
	  'Require Import MinimalSim.Theorem.' \
	  'Definition audited_equivalences := (simulator_halts_iff, blank_simulator_halts_iff).' \
	  'Print Assumptions audited_equivalences.' \
	  'Check simulator_halts_iff.' \
	  'Check blank_simulator_halts_iff.' > "$$audit_dir/Assumptions.v"; \
	$(COQTOP) -quiet -batch $(FLAGS) -l "$$audit_dir/Assumptions.v"
	$(COQCHK) $(COQCHKFLAGS) $(FLAGS) MinimalSim.Theorem

fresh:
	$(MAKE) clean
	$(MAKE) audit

clean:
	rm -f -- *.vo *.vos *.vok *.glob .*.aux .*.cache .coqdeps
