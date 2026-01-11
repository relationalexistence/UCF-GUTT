# UCF/GUTT Extensions Library Makefile
# =====================================
#
# Targets:
#   make          - Build the library
#   make build    - Build the library (src only)
#   make all      - Build everything (src + props + examples)
#   make audit    - Run axiom audit
#   make check    - Verify with coqchk
#   make verify   - Full verification pipeline
#   make install  - Install to user-contrib
#   make docker   - Build Docker container
#   make clean    - Remove build artifacts
#   make stats    - Show library statistics

COQC = coqc
COQCHK = coqchk
COQFLAGS = -w +all -R src UCF.GUTT.Extensions -R props UCF.GUTT.Props

# Source files in dependency order
SRC_FILES = \
	src/Top__Extensions__Base.v \
	src/Top__Extensions__WholeCompletion.v \
	src/Top__Extensions__Composition.v \
	src/Top__Extensions__Prelude.v \
	src/Top__Extensions__Extras.v \
	src/Top__Extensions__axiomaudit.v

PROPS_FILES = \
	props/Proposition_01.v

EXAMPLE_FILES = \
	examples/BasicUsage.v \
	examples/IteratedCompletion.v

SRC_OBJECTS = $(SRC_FILES:.v=.vo)
PROPS_OBJECTS = $(PROPS_FILES:.v=.vo)
EXAMPLE_OBJECTS = $(EXAMPLE_FILES:.v=.vo)

.PHONY: all build props examples audit check verify install docker docker-audit clean stats help

# Default target - build everything
all: build props examples
	@echo ""
	@echo "╔════════════════════════════════════════════════════════════════╗"
	@echo "║  FULL BUILD COMPLETE: 9/9 files compiled                       ║"
	@echo "║    src/       6 files                                          ║"
	@echo "║    props/     1 file                                           ║"
	@echo "║    examples/  2 files                                          ║"
	@echo "╚════════════════════════════════════════════════════════════════╝"

# Build core library only
build: $(SRC_OBJECTS)
	@echo ""
	@echo "╔════════════════════════════════════════════════════════════════╗"
	@echo "║  BUILD COMPLETE: 6/6 src files compiled                        ║"
	@echo "╚════════════════════════════════════════════════════════════════╝"

# Build propositions
props: build $(PROPS_OBJECTS)
	@echo "Propositions compiled."

# Build examples
examples: props $(EXAMPLE_OBJECTS)
	@echo "Examples compiled."

# Pattern rule for src/*.vo files
src/%.vo: src/%.v
	@echo "Compiling $<..."
	$(COQC) $(COQFLAGS) $<

# Pattern rule for props/*.vo files
props/%.vo: props/%.v
	@echo "Compiling $<..."
	$(COQC) $(COQFLAGS) $<

# Pattern rule for examples/*.vo files
examples/%.vo: examples/%.v
	@echo "Compiling $<..."
	$(COQC) $(COQFLAGS) $<

# Dependencies for src/
src/Top__Extensions__WholeCompletion.vo: src/Top__Extensions__Base.vo
src/Top__Extensions__Composition.vo: src/Top__Extensions__Base.vo src/Top__Extensions__WholeCompletion.vo
src/Top__Extensions__Prelude.vo: src/Top__Extensions__Base.vo src/Top__Extensions__WholeCompletion.vo src/Top__Extensions__Composition.vo
src/Top__Extensions__Extras.vo: src/Top__Extensions__Base.vo src/Top__Extensions__WholeCompletion.vo src/Top__Extensions__Composition.vo
src/Top__Extensions__axiomaudit.vo: src/Top__Extensions__Prelude.vo src/Top__Extensions__Extras.vo

# Dependencies for props/
props/Proposition_01.vo: src/Top__Extensions__Prelude.vo

# Dependencies for examples/
examples/BasicUsage.vo: src/Top__Extensions__Prelude.vo src/Top__Extensions__Extras.vo props/Proposition_01.vo
examples/IteratedCompletion.vo: src/Top__Extensions__Prelude.vo src/Top__Extensions__Composition.vo

# Run axiom audit
audit: build
	@echo ""
	@echo "Running axiom audit..."
	@echo ""
	@echo "Checking Print Assumptions output..."
	@$(COQC) $(COQFLAGS) src/Top__Extensions__axiomaudit.v 2>&1 | grep -c "Closed under the global context" | \
		xargs -I {} sh -c 'if [ {} -eq 163 ]; then \
			echo ""; \
			echo "╔════════════════════════════════════════════════════════════════╗"; \
			echo "║  AUDIT PASSED: 163/163 exports closed under global context     ║"; \
			echo "║  AXIOMS: 0                                                     ║"; \
			echo "╚════════════════════════════════════════════════════════════════╝"; \
		else \
			echo "AUDIT FAILED: Expected 163, got {}"; \
			exit 1; \
		fi'

# Verify with coqchk
check: build
	@echo ""
	@echo "Running coqchk verification..."
	@for lib in Base WholeCompletion Composition Prelude Extras axiomaudit; do \
		echo "Checking Top__Extensions__$$lib..."; \
		$(COQCHK) -R src UCF.GUTT.Extensions UCF.GUTT.Extensions.Top__Extensions__$$lib || exit 1; \
	done
	@echo ""
	@echo "╔════════════════════════════════════════════════════════════════╗"
	@echo "║  COQCHK PASSED: 6/6 libraries verified                         ║"
	@echo "╚════════════════════════════════════════════════════════════════╝"

# Full verification pipeline
verify: clean build audit check
	@echo ""
	@echo "╔════════════════════════════════════════════════════════════════╗"
	@echo "║                    FULL VERIFICATION COMPLETE                  ║"
	@echo "╠════════════════════════════════════════════════════════════════╣"
	@echo "║  Build:    ✅ PASS (6/6 files)                                 ║"
	@echo "║  Audit:    ✅ PASS (163 exports, 0 axioms)                     ║"
	@echo "║  coqchk:   ✅ PASS (6/6 libraries)                             ║"
	@echo "╠════════════════════════════════════════════════════════════════╣"
	@echo "║  STATUS:   ZERO AXIOMS — LIBRARY QUALITY                       ║"
	@echo "╚════════════════════════════════════════════════════════════════╝"

# Install to user-contrib
install: build
	@echo "Installing to Coq user-contrib..."
	@mkdir -p $(COQLIB)/user-contrib/UCF/GUTT/Extensions
	@cp src/*.vo $(COQLIB)/user-contrib/UCF/GUTT/Extensions/
	@cp src/*.v $(COQLIB)/user-contrib/UCF/GUTT/Extensions/
	@echo "Installed to $(COQLIB)/user-contrib/UCF/GUTT/Extensions/"

# Build Docker container
docker:
	@echo "Building Docker container..."
	docker build -t ucf-gutt-extensions:1.0 .
	@echo ""
	@echo "Container built: ucf-gutt-extensions:1.0"
	@echo "Run with: docker run ucf-gutt-extensions:1.0"

# Run audit in Docker
docker-audit: docker
	docker run ucf-gutt-extensions:1.0 audit

# Clean build artifacts
clean:
	@echo "Cleaning build artifacts..."
	@rm -f src/*.vo src/*.vok src/*.vos src/*.glob src/.*.aux
	@rm -f props/*.vo props/*.vok props/*.vos props/*.glob props/.*.aux
	@rm -f examples/*.vo examples/*.vok examples/*.vos examples/*.glob examples/.*.aux
	@echo "Clean complete."

# Show library statistics
stats:
	@echo ""
	@echo "UCF/GUTT Extensions Library Statistics"
	@echo "======================================="
	@echo ""
	@echo "Source (src/):"
	@wc -l src/*.v | tail -1
	@echo ""
	@echo "Propositions (props/):"
	@wc -l props/*.v | tail -1
	@echo ""
	@echo "Examples (examples/):"
	@wc -l examples/*.v | tail -1
	@echo ""
	@echo "Total:"
	@wc -l src/*.v props/*.v examples/*.v | tail -1
	@echo ""
	@echo "Proofs (Qed/Defined):"
	@grep -c "Qed\.\|Defined\." src/*.v props/*.v examples/*.v 2>/dev/null | awk -F: '{sum+=$$2} END {print "  " sum}'

# Help
help:
	@echo "UCF/GUTT Extensions Library"
	@echo ""
	@echo "Targets:"
	@echo "  make          Build everything (src + props + examples)"
	@echo "  make all      Build everything (src + props + examples)"
	@echo "  make build    Build core library only (src/)"
	@echo "  make props    Build propositions (props/)"
	@echo "  make examples Build examples (examples/)"
	@echo "  make audit    Run axiom audit (163 exports)"
	@echo "  make check    Verify with coqchk"
	@echo "  make verify   Full verification (build + audit + check)"
	@echo "  make install  Install to user-contrib"
	@echo "  make docker   Build Docker container"
	@echo "  make clean    Remove build artifacts"
	@echo "  make stats    Show library statistics"
	@echo "  make help     Show this help"
