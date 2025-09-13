#!/usr/bin/env bash
set -euo pipefail

# Simple all-in-one Coq build for this repo
# - Uses OPAM if Coq isn't installed
# - Installs Coq 8.19.2 into its own switch
# - Then builds via root Makefile

COQ_SWITCH="coq-8.19.2"
COQ_PKG="coq.8.19.2"

have() { command -v "$1" >/dev/null 2>&1; }

if ! have coqc || ! have coq_makefile; then
  if have opam; then
    echo "[setup] Creating OPAM switch ${COQ_SWITCH} (if needed)…"
    if ! opam switch list --short | grep -qx "${COQ_SWITCH}"; then
      opam switch create "${COQ_SWITCH}" ocaml-base-compiler.5.1.1
    fi
    eval "$(opam env --switch=${COQ_SWITCH})"
    opam repo add coq-released https://coq.inria.fr/opam/released || true
    opam install -y "${COQ_PKG}"
  else
    echo "✗ Coq not found and OPAM is not installed."
    echo "  Please install OPAM (https://opam.ocaml.org) or install Coq (>=8.18) via your package manager,"
    echo "  then re-run:  make coq   (or)   scripts/build.sh"
    exit 1
  fi
fi

echo "[build] Building Coq proofs…"
make coq
echo "✓ Done."
