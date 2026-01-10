# UCF/GUTT Extensions Library Makefile
# =====================================
#
# Targets:
#   make          - Build the library
#   make build    - Build the library
#   make audit    - Run axiom audit (163 exports)
#   make check    - Verify with coqchk
#   make verify   - Full verification pipeline
#   make install  - Install to user-contrib
#   make docker   - Build Docker container
#   make clean    - Remove build artifacts
#   make stats    - Show library statistics

COQC = coqc
COQCHK = coqchk
COQFLAGS = -w +all -R src UCF.GUTT.Extensions

# Source files in dependency order
SOURCES = \
	src/Top__Extensions__Base.v \
	src/Top__Extensions__WholeCompletion.v \
	src/Top__Extensions__Composition.v \
	src/Top__Extensions__Prelude.v \
	src/Top__Extensions__Extras.v \
	src/Top__Extensions__axiomaudit.v

OBJECTS = $(SOURCES:.v=.vo)

.PHONY: all build audit check verify install docker docker-audit clean stats help

# Default target
all: build

# Build the library
build: $(OBJECTS)
	@echo ""
	@echo "╔════════════════════════════════════════════════════════════════╗"
	@echo "║  BUILD COMPLETE: 6/6 files compiled                            ║"
	@echo "╚════════════════════════════════════════════════════════════════╝"

# Pattern rule for .vo files
src/%.vo: src/%.v
	@echo "Compiling $<..."
	$(COQC) $(COQFLAGS) $<

# Dependencies
src/Top__Extensions__WholeCompletion.vo: src/Top__Extensions__Base.vo
src/Top__Extensions__Composition.vo: src/Top__Extensions__Base.vo src/Top__Extensions__WholeCompletion.vo
src/Top__Extensions__Prelude.vo: src/Top__Extensions__Base.vo src/Top__Extensions__WholeCompletion.vo src/Top__Extensions__Composition.vo
src/Top__Extensions__Extras.vo: src/Top__Extensions__Base.vo src/Top__Extensions__WholeCompletion.vo src/Top__Extensions__Composition.vo
src/Top__Extensions__axiomaudit.vo: src/Top__Extensions__Prelude.vo src/Top__Extensions__Extras.vo

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
	@echo "Clean complete."

# Show library statistics
stats:
	@echo ""
	@echo "UCF/GUTT Extensions Library Statistics"
	@echo "======================================="
	@echo ""
	@wc -l src/*.v | tail -1
	@echo ""
	@echo "Definitions/Fixpoints:"
	@grep -c "Definition\|Fixpoint" src/*.v | awk -F: '{sum+=$$2} END {print "  " sum}'
	@echo "Lemmas/Theorems:"
	@grep -c "Lemma\|Theorem" src/*.v | awk -F: '{sum+=$$2} END {print "  " sum}'
	@echo "Records:"
	@grep -c "^Record" src/*.v | awk -F: '{sum+=$$2} END {print "  " sum}'
	@echo "Examples:"
	@grep -c "Example" src/*.v | awk -F: '{sum+=$$2} END {print "  " sum}'

# Help
help:
	@echo "UCF/GUTT Extensions Library"
	@echo ""
	@echo "Targets:"
	@echo "  make          Build the library"
	@echo "  make build    Build the library"
	@echo "  make audit    Run axiom audit (163 exports)"
	@echo "  make check    Verify with coqchk"
	@echo "  make verify   Full verification (build + audit + check)"
	@echo "  make install  Install to user-contrib"
	@echo "  make docker   Build Docker container"
	@echo "  make clean    Remove build artifacts"
	@echo "  make stats    Show library statistics"
	@echo "  make help     Show this help"
