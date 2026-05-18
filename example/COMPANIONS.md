# UCF/GUTT — Executable Companions

This file indexes the Python modules that serve as **executable companions**
to the UCF/GUTT Coq library. Each one mirrors a specific slice of the
formally verified content, with exact arithmetic where applicable and no
classical content. The proofs live in Coq; the companions let a reader
*see* what the formal theorems are asserting, on concrete inputs, without
having to read Coq.

The companions are not substitutes for the Coq library. They are
narrowly scoped demonstration artifacts whose claims correspond
one-to-one to named theorems in the public Coq core.

---

## Index

| Module                   | Version | Scope                                                                  | README                                     |
|--------------------------|---------|------------------------------------------------------------------------|--------------------------------------------|
| `Ucf_math_demos.py`      | v1.0.0  | Numbers & irrationals: √2 ∉ ℚ, Euclid in N_rel, totalized division     | [README](./Ucf_math_demos_README.md)       |
| `RE_in_a_teacup_v3.py`   | v3.0.0  | Reality Engine miniature: proposition firing, DERIVED guards, exports  | [README](./RE_in_a_teacup_v3_README.md)    |

---

## What each one is for

### `Ucf_math_demos.py` — the arithmetic/numbers companion

Three demos that mirror specific theorems from the Coq numbers core:

- **Parity descent + Newton iteration in Q** for √2 ∉ ℚ
  (`Top__Numbers__RelationalIrrationals.v`).
- **Euclid's infinitude-of-primes construction** over N_rel, exhibiting
  each new prime as the smallest prime factor of the product-plus-one
  (`Top__Numbers__Relational.v` + `RelationalIntegers.v`).
- **Totalized division** routing `1/0` through three relational contexts
  (`RC_Space`, `RC_Time`, `RC_Info`) with full truth table
  (`Top__Numbers__RelationalDivision.v`).

All arithmetic exact via `fractions.Fraction`. No external dependencies.

### `RE_in_a_teacup_v3.py` — the relational-proposition companion

A miniature of the v2.0 Reality Engine architecture. Builds a
`RelationalTensor` from a finite relational system (binary edges plus
arbitrary-arity hyperedges) and reports which CORE propositions fire
with what witnesses:

- **P1** Seriality via Whole-completion (`Top__Propositions__Prop_01`) — unconditional root
- **P2** Multi-dimensional representation / DSoR (`Top__Propositions__Prop_02`) — binary-content-sensitive
- **P4** Graph / Adjacency Tensor (`Top__Propositions__Prop_04`)
- **P5** Relational Tensor / NRT modular composition (`Top__Propositions__Prop_05`)
- **P7** Hyper-arity (Coq formalization pending)
- **P10** Directionality (`Top__Propositions__Prop_10`) — binary-content-sensitive

Plus a DERIVED proposition layer with three-state guards (`D_eq`,
`D_fun`), a smoke test validating every system in the registry against
expected firing patterns, and an export mode that writes Coq cross-check
examples (`firings.v`), a LaTeX table (`firings.tex`), and a
`CITATION.cff`.

---

## Adding a new companion

When a new executable companion is added to the repository:

1. Place the Python file at the repo root (or a documented subdirectory).
2. Give it a version stamp in the file header (e.g. `# Version: v1.0.0`).
3. Write a dedicated README (`<module_name>_README.md`) covering scope,
   demos, Coq correspondence, citation, and license.
4. Add a row to the **Index** table above with module, version, scope,
   and README link.
5. Add a short subsection under **What each one is for** explaining
   what it covers and which Coq files it mirrors.

Keep the scope discipline strict: each companion should claim only what
it demonstrates, and direct framework-level questions to the Coq core or
to the appropriate sibling companion.

---

## Relation to the wider ecosystem

UCF/GUTT has Python projects beyond the executable companions indexed
here — LANTOSE (linguistic workbench), `fhoc` (Formal Harmonic Overlap
Certification), ONA (organizational network analysis), and others. Those
are *applications* of the framework: larger codebases with their own
runtimes, dependencies, and use cases. The companions in this index are
deliberately narrower — small files that exist to make specific Coq
theorems visible and runnable in under a second.

---

## License

All companions are licensed Apache-2.0. © 2023–2026 Michael Fillippini.

The names **UCF/GUTT**, **GUTT-L**, **LANTOSE**, **NRTML**, **RCTT**, and
**Relational Existence** are trademarks of Michael Fillippini; the
Apache 2.0 license grants no rights in these trademarks.

For the Coq substrate, see the public core at
<https://github.com/relationalexistence/UCF-GUTT>. For framework
background, see <https://relationalexistence.com>.
