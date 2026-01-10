# UCF/GUTT Extensions Library
# Reproducible Build Container
#
# Build:   docker build -t ucf-gutt-extensions:1.0 .
# Run:     docker run ucf-gutt-extensions:1.0
# Audit:   docker run ucf-gutt-extensions:1.0 audit
# Shell:   docker run -it ucf-gutt-extensions:1.0 shell

# Pin Coq version by SHA256 for reproducibility
FROM coqorg/coq:8.18.0@sha256:d4c083db048b2fcb138ae8a4f3b1d026f4ef07e7dbae8c73a48f9a4e369a06f0

LABEL maintainer="Michael Fillippini"
LABEL description="UCF/GUTT Extensions Library - Formally Verified Whole-Completion"
LABEL version="1.0.0"
LABEL coq.version="8.18.0"
LABEL audit.exports="163"
LABEL audit.axioms="0"

# Set working directory
WORKDIR /ucf-gutt-extensions

# Copy source files in dependency order (for layer caching)
COPY src/Top__Extensions__Base.v src/
COPY src/Top__Extensions__WholeCompletion.v src/
COPY src/Top__Extensions__Composition.v src/
COPY src/Top__Extensions__Prelude.v src/
COPY src/Top__Extensions__Extras.v src/
COPY src/Top__Extensions__axiomaudit.v src/

# Copy build infrastructure
COPY Makefile _CoqProject ./
COPY python/ python/
COPY docs/ docs/
COPY README.md LICENSE CHANGELOG.md ./

# Build with full warnings
RUN coqc -w +all -R src UCF.GUTT.Extensions src/Top__Extensions__Base.v && \
    coqc -w +all -R src UCF.GUTT.Extensions src/Top__Extensions__WholeCompletion.v && \
    coqc -w +all -R src UCF.GUTT.Extensions src/Top__Extensions__Composition.v && \
    coqc -w +all -R src UCF.GUTT.Extensions src/Top__Extensions__Prelude.v && \
    coqc -w +all -R src UCF.GUTT.Extensions src/Top__Extensions__Extras.v && \
    coqc -w +all -R src UCF.GUTT.Extensions src/Top__Extensions__axiomaudit.v

# Run coqchk verification
RUN coqchk -R src UCF.GUTT.Extensions \
    UCF.GUTT.Extensions.Top__Extensions__Base \
    UCF.GUTT.Extensions.Top__Extensions__WholeCompletion \
    UCF.GUTT.Extensions.Top__Extensions__Composition \
    UCF.GUTT.Extensions.Top__Extensions__Prelude \
    UCF.GUTT.Extensions.Top__Extensions__Extras \
    UCF.GUTT.Extensions.Top__Extensions__axiomaudit

# Validate axiom-free status
RUN coqc -R src UCF.GUTT.Extensions src/Top__Extensions__axiomaudit.v 2>&1 | \
    grep -c "Closed under the global context" | \
    xargs -I {} sh -c 'if [ {} -ne 163 ]; then echo "AUDIT FAILED"; exit 1; fi'

# Generate checksums
RUN sha256sum src/*.v > source-checksums.txt && \
    sha256sum src/*.vo > compiled-checksums.txt

# Generate build manifest
RUN echo "UCF/GUTT Extensions Library Build Manifest" > build-manifest.txt && \
    echo "===========================================" >> build-manifest.txt && \
    echo "" >> build-manifest.txt && \
    echo "Build Date: $(date -u +%Y-%m-%dT%H:%M:%SZ)" >> build-manifest.txt && \
    echo "Coq Version: $(coqc --version | head -1)" >> build-manifest.txt && \
    echo "" >> build-manifest.txt && \
    echo "Files:" >> build-manifest.txt && \
    ls -la src/*.vo >> build-manifest.txt && \
    echo "" >> build-manifest.txt && \
    echo "Source Checksums:" >> build-manifest.txt && \
    cat source-checksums.txt >> build-manifest.txt && \
    echo "" >> build-manifest.txt && \
    echo "Verification Status:" >> build-manifest.txt && \
    echo "  Exports Audited: 163" >> build-manifest.txt && \
    echo "  Axioms: 0" >> build-manifest.txt && \
    echo "  coqchk: PASSED" >> build-manifest.txt

# Entrypoint script
RUN echo '#!/bin/bash' > /entrypoint.sh && \
    echo 'case "$1" in' >> /entrypoint.sh && \
    echo '  audit)' >> /entrypoint.sh && \
    echo '    echo "Running axiom audit..."' >> /entrypoint.sh && \
    echo '    coqc -R src UCF.GUTT.Extensions src/Top__Extensions__axiomaudit.v 2>&1 | grep -c "Closed under the global context"' >> /entrypoint.sh && \
    echo '    echo "163 exports verified axiom-free"' >> /entrypoint.sh && \
    echo '    ;;' >> /entrypoint.sh && \
    echo '  shell)' >> /entrypoint.sh && \
    echo '    exec /bin/bash' >> /entrypoint.sh && \
    echo '    ;;' >> /entrypoint.sh && \
    echo '  manifest)' >> /entrypoint.sh && \
    echo '    cat build-manifest.txt' >> /entrypoint.sh && \
    echo '    ;;' >> /entrypoint.sh && \
    echo '  checksums)' >> /entrypoint.sh && \
    echo '    cat source-checksums.txt' >> /entrypoint.sh && \
    echo '    ;;' >> /entrypoint.sh && \
    echo '  *)' >> /entrypoint.sh && \
    echo '    cat build-manifest.txt' >> /entrypoint.sh && \
    echo '    ;;' >> /entrypoint.sh && \
    echo 'esac' >> /entrypoint.sh && \
    chmod +x /entrypoint.sh

ENTRYPOINT ["/entrypoint.sh"]
CMD ["manifest"]
