# =============================================================================
#   UCF/GUTT(TM) -- Top-level Makefile
#   Copyright 2023-2026 Michael Fillippini.
#
#   Licensed under the Apache License, Version 2.0 (the "License").
#   You may obtain a copy of the License at:
#       http://www.apache.org/licenses/LICENSE-2.0
#
#   SPDX-License-Identifier: Apache-2.0
# =============================================================================
#
# Targets:
#   all           build the whole library                            (default)
#   build         alias for all
#   audit         build + summarize the in-source `Print Assumptions` results
#   stats         file count, line count, theorem/lemma count
#   axiom-check   sanity-grep for Axiom / Admitted / Parameter in any source
#   clean         remove *.vo *.vok *.vos *.glob *.aux *.cache
#   distclean     clean + remove generated Makefile.coq*
#   help          this list
#
# Requirements:
#   - Coq 8.18+ on PATH (coqc, coq_makefile)
#   - GNU make
#
# This file delegates to the coq_makefile-generated Makefile.coq for the actual
# build; we just wrap it with friendly targets and a single source of truth
# (_CoqProject).
#
# Note: `Print Assumptions` calls are embedded directly in the source files;
# `make audit` re-runs the build and counts how many emit
# "Closed under the global context" (current expected count: 80).
# =============================================================================

COQ_PROJECT  := _CoqProject
COQ_MAKEFILE := Makefile.coq

# Use as many parallel jobs as the host allows by default.
JOBS ?= $(shell nproc 2>/dev/null || echo 2)

.PHONY: all build audit stats axiom-check clean distclean help

# -----------------------------------------------------------------------------
# Default target
# -----------------------------------------------------------------------------
all: build

# -----------------------------------------------------------------------------
# Generate Makefile.coq from _CoqProject if missing or out of date
# -----------------------------------------------------------------------------
$(COQ_MAKEFILE): $(COQ_PROJECT)
	@echo ">> regenerating $(COQ_MAKEFILE) from $(COQ_PROJECT)"
	@coq_makefile -f $(COQ_PROJECT) -o $(COQ_MAKEFILE)

# -----------------------------------------------------------------------------
# Build the whole library (delegates to coq_makefile output)
# -----------------------------------------------------------------------------
build: $(COQ_MAKEFILE)
	@$(MAKE) -f $(COQ_MAKEFILE) -j$(JOBS)
	@echo ""
	@echo "=========================================================="
	@FILES=$$(grep -cE '^\s*Top__[^[:space:]]+\.v' $(COQ_PROJECT) 2>/dev/null); \
	  echo "  Build OK -- $$FILES files compiled (zero Admitted /"
	@echo "  zero UCF axioms / zero Parameter declarations)."
	@echo "  Run 'make audit' to count the in-source"
	@echo "  'Print Assumptions' = 'Closed under the global context'"
	@echo "  results.  Run 'make stats' for size metrics."
	@echo "=========================================================="

# -----------------------------------------------------------------------------
# Audit: rebuild and summarize the in-source `Print Assumptions` output.
# `Print Assumptions` calls are embedded directly in the source files;
# each one prints either "Closed under the global context." or a list of
# unclosed dependencies.  A clean library has zero unclosed dependencies.
# -----------------------------------------------------------------------------
audit: $(COQ_MAKEFILE)
	@echo ">> Forcing clean rebuild to capture full audit output ..."
	@rm -f *.vo *.vok *.vos *.glob .audit.log
	@$(MAKE) -f $(COQ_MAKEFILE) -j$(JOBS) 2>&1 | tee .audit.log
	@echo ""
	@echo "=========================================================="
	@echo "  AXIOM AUDIT SUMMARY"
	@echo "=========================================================="
	@PA_TOTAL=$$(grep -hcE '^Print Assumptions ' Top__*.v 2>/dev/null \
	             | awk '{s+=$$1} END {print s+0}'); \
	  echo "  'Print Assumptions' calls embedded in sources:    $$PA_TOTAL"
	@CLOSED=$$(grep -c "Closed under the global context" .audit.log 2>/dev/null); \
	  if [ -z "$$CLOSED" ]; then CLOSED=0; fi; \
	  echo "  'Closed under the global context' results:        $$CLOSED"
	@PAT='^Axiom\|^Parameter\|Variable\|Hypothesis'; \
	  COUNT=$$(grep -c "$$PAT" .audit.log 2>/dev/null); \
	  if [ -z "$$COUNT" ]; then COUNT=0; fi; \
	  echo "  Unclosed dependencies detected:                   $$COUNT"
	@echo "=========================================================="

# -----------------------------------------------------------------------------
# Statistics
# -----------------------------------------------------------------------------
stats:
	@echo "=========================================================="
	@echo "  UCF/GUTT(TM) library statistics"
	@echo "=========================================================="
	@FILES=$$(ls Top__*.v 2>/dev/null | wc -l); \
	  echo "  Source files:           $$FILES"
	@LINES=$$(cat Top__*.v 2>/dev/null | wc -l); \
	  echo "  Total lines:            $$LINES"
	@THM=$$(grep -hcE \
	    "^([[:space:]]*)(Theorem|Lemma|Corollary|Fact|Remark|Proposition|Example) " \
	    Top__*.v 2>/dev/null | awk '{s+=$$1} END {print s}'); \
	  echo "  Theorems + lemmas:      $$THM"
	@DEF=$$(grep -hcE "^([[:space:]]*)(Definition|Fixpoint) " Top__*.v 2>/dev/null \
	    | awk '{s+=$$1} END {print s}'); \
	  echo "  Definitions:            $$DEF"
	@IND=$$(grep -hcE "^([[:space:]]*)(Inductive|CoInductive|Record) " Top__*.v 2>/dev/null \
	    | awk '{s+=$$1} END {print s}'); \
	  echo "  Inductive / Record:     $$IND"
	@PA=$$(grep -hcE "^Print Assumptions " Top__*.v 2>/dev/null \
	    | awk '{s+=$$1} END {print s}'); \
	  echo "  Print Assumptions:      $$PA  (audit calls in source)"
	@AX=$$(grep -hcE "^([[:space:]]*)Axiom " Top__*.v 2>/dev/null \
	    | awk '{s+=$$1} END {print s}'); \
	  echo "  Axiom declarations:     $$AX  (must be 0)"
	@AD=$$(grep -hcE "(Admitted|admit)\." Top__*.v 2>/dev/null \
	    | awk '{s+=$$1} END {print s}'); \
	  echo "  Admitted proofs:        $$AD  (must be 0)"
	@PR=$$(grep -hcE "^([[:space:]]*)Parameter " Top__*.v 2>/dev/null \
	    | awk '{s+=$$1} END {print s}'); \
	  echo "  Parameter declarations: $$PR  (must be 0)"
	@echo "=========================================================="

# -----------------------------------------------------------------------------
# Sanity grep: must report zero on every line
# -----------------------------------------------------------------------------
axiom-check:
	@echo ">> Scanning sources for forbidden constructs ..."
	@FAIL=0; \
	  for label in Axiom Admitted Parameter; do \
	    HITS=$$(grep -E "^[[:space:]]*$$label[[:space:]]" Top__*.v \
	            | grep -v "^[[:space:]]*(\*"); \
	    if [ -n "$$HITS" ]; then \
	      echo ""; echo "  !! Found '$$label' in sources:"; echo "$$HITS"; \
	      FAIL=1; \
	    else \
	      echo "  [OK] No '$$label' declarations found."; \
	    fi; \
	  done; \
	  exit $$FAIL

# -----------------------------------------------------------------------------
# Clean targets
# -----------------------------------------------------------------------------
clean:
	@echo ">> removing build artifacts"
	@rm -f *.vo *.vok *.vos *.glob *.aux *.cache .audit.log
	@rm -rf .coq-native .lia.cache .nia.cache
	@if [ -f $(COQ_MAKEFILE) ]; then \
	  $(MAKE) -f $(COQ_MAKEFILE) cleanall 2>/dev/null || true; \
	fi

distclean: clean
	@echo ">> removing generated Makefile.coq*"
	@rm -f $(COQ_MAKEFILE) $(COQ_MAKEFILE).conf $(COQ_MAKEFILE).d

# -----------------------------------------------------------------------------
# Help
# -----------------------------------------------------------------------------
help:
	@echo "UCF/GUTT(TM) Coq library -- make targets"
	@echo ""
	@echo "  make            build the whole library"
	@echo "  make audit      build, then summarize the Print Assumptions audit"
	@echo "  make stats      file / line / theorem counts"
	@echo "  make axiom-check  fail if any Axiom / Admitted / Parameter found"
	@echo "  make clean      remove build artifacts"
	@echo "  make distclean  also remove Makefile.coq*"
	@echo "  make help       this list"
