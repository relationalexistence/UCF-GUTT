# UCF/GUTT — Coq Library (Public Core)

> **Unified Conceptual Framework / Grand Unified Tensor Theory**
> A relational ontology in which relations are treated as constitutively
> fundamental.  This repository contains the machine-checked Coq library
> for the public core of the framework — Extensions, Numbers, Relations,
> Propositions 1/2/4/5/10 (plus Clock Hierarchy Coherence), and the
> Relational Cubical Type Theory (RCTT) stack.

- **Version:** 2.0.0 / Coq 8.18+
- **License:** [Apache License 2.0](LICENSE) — see also [`NOTICE`](NOTICE).
  Trademark policy (UCF/GUTT™, GUTT-L™, LANTOSE™, NRTML™, RCTT™,
  Relational Existence™) is in [`TRADEMARKS.md`](TRADEMARKS.md).
  © 2023–2026 Michael Fillippini.
- **Status:** **Zero UCF/GUTT-introduced axioms.  Zero Admitted proofs.
  Zero Parameter declarations.**  30 files, 25,487 lines, 1,230 theorems
  and lemmas, 1,390 definitions — no additional axioms beyond Coq's
  Calculus of Inductive Constructions and the definitional content of
  the imported standard-library modules.

---

## Quickstart

```bash
# Requirements: Coq 8.18+ on PATH (coqc, coq_makefile)
make            # build all 30 files
make stats      # file / line / theorem counts
make axiom-check  # static grep for Axiom / Admitted / Parameter
make clean      # remove *.vo *.vok *.vos *.glob *.aux *.cache
```

A clean build takes well under a minute on a typical host (~38 seconds
single-core, `-j1`, on a 1-core Ubuntu sandbox; faster with `-j` on
multi-core hosts).  Eighty `Print Assumptions` calls are embedded
directly in the source files themselves; a clean build emits
**80 lines of `Closed under the global context.`**

---

## Verification results

The numbers below are from a clean rebuild of the exact source set in
this repository, top of tree.  They are reproducible: `make clean && make`
on Coq 8.18 will produce them.

**Environment**

| Component       | Version                  |
|-----------------|--------------------------|
| Coq             | 8.18.0                   |
| OCaml runtime   | 4.14.1 (Coq's own)       |
| GNU make        | 4.3                      |
| Host            | 1-core sandbox (Ubuntu)  |

**Build**

| Metric                                        | Value           |
|-----------------------------------------------|-----------------|
| Source files (`.v`)                           | 30              |
| Files compiled successfully                   | 30 / 30         |
| Clean rebuild wall time (`-j1`)               | 38 s            |
| Build exit code                               | 0               |
| Compile-time warnings                         | 0               |
| Compile-time errors                           | 0               |

**Axiom audit (in-source `Print Assumptions`)**

`Print Assumptions` calls are embedded directly in the source files, distributed
across the seventeen modules where they certify the principal theorems of each
layer.  Every call returns `Closed under the global context.`

| Module                                          | `Print Assumptions` calls |
|-------------------------------------------------|--------------------------:|
| `Top__Extensions__Composition.v`                | 3                         |
| `Top__Extensions__RelationalUIP.v`              | 7                         |
| `Top__Extensions__Adjunction.v`                 | 3                         |
| `Top__Numbers__UCF_Lia.v`                       | 4                         |
| `Top__Numbers__UCF_Nia.v`                       | 1                         |
| `Top__Numbers__RelationalReals.v`               | 6                         |
| `Top__Numbers__RelationalDivision.v`            | 5                         |
| `Top__Numbers__RelationalIrrationals.v`         | 6                         |
| `Top__Numbers__RelationalIntegers.v`            | 3                         |
| `Top__Numbers__RelationalRationals.v`           | 7                         |
| `Top__Relations__RelationalAlgebra.v`           | 5                         |
| `Top__Propositions__Prop_01.v`                  | 4                         |
| `Top__Propositions__Prop_05.v`                  | 5                         |
| `Top__Propositions__Prop_10.v`                  | 8                         |
| `Top__Cubical__NCube.v`                         | 4                         |
| `Top__Cubical__KanCanonical.v`                  | 5                         |
| `Top__Cubical__RCTT.v`                          | 4                         |
| —                                               | —                         |
| **Total**                                       | **80**                    |
| **Closed under the global context**             | **80 / 80**               |

**Static-grep audit (`make axiom-check`)**

| Construct              | Hits |
|------------------------|-----:|
| `Axiom` declarations   | 0    |
| `Admitted` proofs      | 0    |
| `Parameter` declarations | 0  |

**Kernel-level re-verification (`coqchk`)**

`coqchk` independently re-verifies the compiled `.vo` files outside the
elaborator, replaying every constant against the trusted kernel.  A
single invocation over the full library —

```
coqchk -R . "" $(ls Top__*.v | sed 's/\.v$//')
```

— re-verifies **all 30 modules** and terminates with:

```
Modules were successfully checked
```

Representative top-of-stack capstones re-verify individually as well:

| Module                                          | `coqchk` exit |
|-------------------------------------------------|---------------|
| `Top__Cubical__RCTT`                            | 0             |
| `Top__Cubical__KanCanonical`                    | 0             |
| `Top__Propositions__Prop_05`                    | 0             |
| `Top__Propositions__ClockHierarchyCoherence`    | 0             |

**Library size (`make stats`)**

| Metric                       | Value     |
|------------------------------|----------:|
| Source files                 | 30        |
| Total lines                  | 25,487    |
| Theorems + lemmas            | 1,230     |
| Definitions / Fixpoints      | 1,390     |
| Inductives / Records         | 34        |
| `Axiom`                      | 0         |
| `Admitted`                   | 0         |
| `Parameter`                  | 0         |

What "Closed under the global context" means concretely:

- No `Axiom` declarations anywhere in the 30 sources.
- No `Admitted` proofs.
- No top-level `Parameter` (the constants used in physics-style modules
  outside this core are not in scope here).
- No reliance on the axiom of choice, propositional extensionality,
  functional extensionality, proof irrelevance, or classical logic.
- No additional axioms beyond Coq's Calculus of Inductive Constructions
  and the definitional content of the imported standard-library modules
  (`Coq.Arith`, `Coq.ZArith`, `Coq.QArith`, `Coq.Lists.List`,
  `Coq.micromega.Lia`, `Coq.Classes.*`, `Coq.Setoids.Setoid`,
  `Coq.Bool.Bool`, `Coq.Relations.Relation_*`, `Coq.setoid_ring.*`,
  `Coq.Logic.Eqdep_dec`).

---

## What this public core does *not* include

This repository ships the verified mathematical substrate.  It deliberately
omits the commercial and applied layers of the framework:

- Reality Engine internals (proposition-firing engine, applicability
  predicates as tensor-invariant queries).
- `fhoc` (Formal Harmonic Overlap Certification) internals.
- LANTOSE linguistic workbench internals (NRTML, n-stratum engine, MDF
  ingestion, ML translation).
- The Relational Stability Function (Φ) and Relational Connectivity
  Graph (RCG) internals.
- Application-layer Coq files: Marcus electron-transfer chain, Layer-11
  physics derivations (Lagrangian, Schrödinger, Standard Model, QFT
  renormalization), and the larger `Top__Applications__*` and
  `Top__Cubical__*Beyond*` modules.
- Customer schemas, industrial integration code, proprietary datasets,
  and NDA-level derivation chains.

The 30 files in this repository are the public substrate against which
the rest of the framework is layered.

---

## Interpretation of scope

The theorems in this repository establish **formal results under the
definitions provided in the library**.  They should not be read as
empirical claims about physical, biological, psychological, or industrial
systems unless explicitly paired with a separate application module and
its own validation protocol.  Terms used internally — *seriality*,
*whole-completion*, *clock hierarchy*, *relational univalence*, *tensor*,
*directionality* — are defined precisely in their respective source
files; their relationship to similarly-named concepts in other
disciplines (HoTT/UF, mathematical physics, category theory, network
science) is a matter of separate interpretive work, not of these proofs.

---

## Repository layout

This is a flat layout: every source file lives in the repository root with a
fully-qualified name encoded into its filename (`__` is the directory
separator, equivalent to a dot in the logical Coq module path).  The
loadpath is declared in `_CoqProject` as `-Q . ""`, so
`Top__Extensions__Base.v` is loaded by `Require Import Top__Extensions__Base.`

```
ucf-gutt/
├── _CoqProject              authoritative file list + load path
├── Makefile                 top-level user-facing wrapper
├── Makefile.coq             auto-generated by `coq_makefile` (do not edit)
├── README.md                this file
└── Top__*.v                 30 source files (see Layer table below)
```

---

## Layer dependency DAG

The library is organized into **13 acyclic layers, numbered 0–12**.
`_CoqProject` lists the files in topologically-sorted order so a `make -jN`
build is correct under any parallelism level.

| Layer | Files                                                                                                   | Role                                    |
|------:|---------------------------------------------------------------------------------------------------------|-----------------------------------------|
| 0     | `Base`, `UCF_Lia`, `Prop_10`                                                                            | Foundations (stdlib only)               |
| 1     | `WholeCompletion`, `UCF_Nia`                                                                            | Single-step deps                        |
| 2     | `Composition`                                                                                           | Universe-extension composition          |
| 3     | `Prelude`, `Extras`                                                                                     | Re-export umbrella + closures / decid.  |
| 4     | `RelationalUIP`, `Relational`, `RelationalReals`, `Prop_01`, `Cubical.Interval`                         | Prelude consumers                       |
| 5     | `RelationalDivision`, `RelationalIrrationals`, `Prop_02`, `Prop_04`, `Adjunction`, `RelationalAlgebra`  | First applications                      |
| 6     | `RelationalIntegers`, `Weighted`, `Cubical.PathType`                                                    | Integers / weighted relations / paths   |
| 7     | `RelationalRationals`, `Cubical.Univalence`                                                             | Rationals / univalence                  |
| 8     | `ClockHierarchyCoherence`                                                                               | Hierarchical clocks                     |
| 9     | `Prop_05`                                                                                               | Tensors (NRT, RT, DRT, DynamicNRT)      |
| 10    | `Cubical.NCube`                                                                                         | n-Cubes from canonical relations        |
| 11    | `Cubical.JRule`, `Cubical.KanCanonical`                                                                 | J-rule / canonical Kan filling          |
| 12    | `Cubical.RCTT`                                                                                          | RCTT umbrella (re-exports all cubical)  |

---

## What is verified

### Numbers, constructively
- **Naturals (`N_rel`)** — relational successor with `to_nat`/`from_nat`
  isomorphism, full algebra (associativity, commutativity, cancellation).
- **Integers (`Z_rel`)** — pair-quotient construction, equivalence relation
  preserved across `+`, `-`, `*`.
- **Rationals (`Q_rel`)** — bi-faithful with `QArith`'s `Q` via `to_Q`,
  `from_Q`, `to_Q_faithful`, `from_to_Q`, `to_from_Q`.
- **Cauchy Reals (`R_cauchy`)** — Cauchy-modulus sequences, full
  Equivalence instance on `Req`, embedding `Q_to_R` is a ring hom over `Req`.
- **Irrationals** — the **complete `sqrt(2)` chain**: `sqrt2_seq` is
  positive, in `[1,2]`, Cauchy, its square converges to 2, and there is no
  rational whose square equals 2 (`sqrt2_not_rational_Z`,
  `no_rational_squares_to_2`).
- **`UCF_Lia` / `UCF_Nia`** — project-internal arithmetic tactics over
  `Z`/`Q`, with all supporting ring/order/squares/inverse/positivity lemmas
  fully proven.

### Relations
- **`RelationalAlgebra`** — `Rel A B` as a complete Boolean lattice;
  `(Rel, ;;, rel_id)` is a category (`rel_comp_assoc`, `rel_comp_id_l`,
  `rel_comp_id_r`); converse functor `^~` is an involution; all
  distributivity laws.
- **`Weighted`** — `WeightedRel U := U → U → Q`, with sign, support, lift
  to the whole-completion, conservativity and seriality properties.

### Propositions (52 in the full framework; 6 in this public core)
- **Prop 01 — Seriality / Whole-completion.** `proposition_01`:
  `∀ U R (x : Ux U), ∃ y, R' x y` — every entity has an outgoing edge in
  the completion.  Constructive (`proposition_01_constructive`), `Σ`-typed
  (`proposition_01_sigma`), and weak variants.
- **Prop 02 — Multi-dimensional representation.** Every entity has a
  DSoR (Dimensional System of Relations), generalizing to arbitrary
  dimensions (`dsor_arbitrary_dimension`).
- **Prop 04 — Graph / Adjacency Tensor.** `adjacency_tensor_iff`,
  universal connectivity, no isolated entities under decidable equality.
- **Prop 05 — Tensors / NRT.** `Tensor`, `NRT`, `RelationalTensor`,
  `DynamicRelationalTensor`, `DynamicNRT`; composition is associative,
  empty/unit elements act as identities, modularity, type-independence.
- **Prop 10 — Directionality.** Existence with `Undirected`, `Uni`, `Bi`,
  `Multi` directions; direction is independent of existence;
  add/remove/change-direction preserves existence; every entity relates
  to the universal Whole.
- **Clock Hierarchy Coherence.** `tick_serial`, `tick_functional`,
  `advance_from_initial`, `advance_add`, and the n-step `time_diff`
  pseudometric (triangle inequality, antisymmetry, advance laws).

### Relational Cubical Type Theory (RCTT)
- **Interval (`I_R`)** — `option unit` as the canonical relational
  interval: `i0 = Some tt` (inject), `i1 = None` (Whole), with `meet`,
  `join`, `neg` satisfying full De Morgan duality.  `I_R_serial`,
  `I_R_canonical_path`, `I_R_n_fractal`, `I_R_n_endpoints_distinct`.
- **Path types (`RChain R a b`)** — single steps, transitivity, symmetry,
  reflexive correctness, and lifting through extension isomorphisms.
- **n-Cubes (`RCube n U`)** — canonical n-cube from a base relation,
  conservativity, Kan fillers proven canonical and universal.
- **Univalence** — `relational_univalence` plus `relational_transfer`,
  `relational_J`, identity-type inverses (`RId_inv_left`, …).

  > Here *"relational univalence"* is an internally defined and proved
  > **theorem** of this library, not an assumed HoTT/UF Univalence Axiom.
  > It states a relational-extension-equivalence transfer principle over
  > the internally-defined identity type `RId`; it does not assume, nor
  > require, the type-theoretic Univalence Axiom of Voevodsky.

- **J-Rule and funext** — full path induction (`relational_J_full`,
  `path_induction_flat`), relational `funext` (`rel_funext`),
  `rel_is_2_category`, every relation has a sphere (`every_relation_has_sphere`).

  > Likewise, `rel_funext` is a **proved theorem** about graph-equality of
  > functions in this library, not the assumed functional-extensionality
  > axiom; and `relational_J_full` is a proved analogue of the J-rule in
  > the relational identity system, not Coq's primitive `eq_ind`.

- **Capstones (`Top__Cubical__RCTT.v`)** — `RCTT_interval_derived`,
  `RCTT_kan_is_theorem`, `RCTT_kan_canonical`,
  `RCTT_univalence_is_theorem`, `RCTT_beyond_cubes`,
  `RCTT_fractal_connectivity`.

### Identity and UIP
- **`RelationalUIP`** — Hedberg's theorem (`hedberg_uip`, `hedberg_K`),
  UIP and K for `nat` and `bool`, transport roundtrip, dependent-pair
  injectivity (`inj_pair2_nat`), relational-depth UIP, and the UCF wrapper
  `ucf_eq_rect_eq`.

### Extras (closures, decidability, monadic utilities)
- `Decidability.whole_completion_decidable`,
  `Decidability.carrier_eq_decidable`,
  `Decidability.refl_closure_decidable`, `Decidability.sym_closure_decidable`.
- `Utilities.carrier_map_*`, `Utilities.carrier_bind_*` — `option`-flavored
  functor/monad laws on `UE.Carrier`.

---

## Build prerequisites

| Component       | Version             |
|-----------------|---------------------|
| Coq             | 8.18.0 (tested)     |
| OCaml runtime   | 4.14.x (Coq's own)  |
| GNU make        | any modern version  |
| `coq_makefile`  | bundled with Coq    |

No additional Coq libraries are required.  Only the standard library is
imported (`Coq.Arith`, `Coq.ZArith`, `Coq.QArith`, `Coq.Lists.List`,
`Coq.micromega.Lia`, `Coq.Classes.*`, `Coq.Setoids.Setoid`,
`Coq.Bool.Bool`, `Coq.Relations.Relation_*`, `Coq.setoid_ring.*`,
`Coq.Logic.Eqdep_dec`).

---

## File-by-file inventory

| File                                            | Lines | Notes                                        |
|-------------------------------------------------|------:|----------------------------------------------|
| `Top__Extensions__Base.v`                       |   762 | Relational properties (serial, functional,…) |
| `Top__Extensions__WholeCompletion.v`            |   602 | `UE.Carrier U = option U`, the Whole point   |
| `Top__Extensions__Composition.v`                |   984 | Identity, composition, iter, fractal         |
| `Top__Extensions__Prelude.v`                    |   566 | `Require Export` umbrella + `UE` alias       |
| `Top__Extensions__Extras.v`                     |   772 | Closures, decidability, carrier monad        |
| `Top__Extensions__RelationalUIP.v`              |   381 | Hedberg, UIP for `nat`/`bool`, transport     |
| `Top__Extensions__Adjunction.v`                 |   633 | Galois connection, BoolRel/KRel adjunction   |
| `Top__Numbers__Relational.v`                    |  1429 | `N_rel` with full arithmetic                 |
| `Top__Numbers__RelationalReals.v`               |   867 | Cauchy `R_cauchy`, `Req`, ring laws over `Q` |
| `Top__Numbers__RelationalDivision.v`            |  1040 | Boundary / context / division states         |
| `Top__Numbers__RelationalIntegers.v`            |   955 | `Z_rel`, equivalence, ring axioms            |
| `Top__Numbers__RelationalIrrationals.v`         |  1184 | Constructive `sqrt(2)` + irrationality       |
| `Top__Numbers__RelationalRationals.v`           |  1077 | `Q_rel` with `Q`-bi-faithfulness             |
| `Top__Numbers__UCF_Lia.v`                       |  1339 | Z/Q ring, order, squares, inverse modules    |
| `Top__Numbers__UCF_Nia.v`                       |   470 | Q product/power/division/exp bounds          |
| `Top__Relations__RelationalAlgebra.v`           |  1343 | Boolean lattice + category of relations      |
| `Top__Relations__Weighted.v`                    |   862 | `WeightedRel U`, sign, support, multiplex    |
| `Top__Propositions__Prop_01.v`                  |   922 | Seriality / Whole-completion                 |
| `Top__Propositions__Prop_02.v`                  |   593 | Multi-dimensional representation, DSoR       |
| `Top__Propositions__Prop_04.v`                  |   861 | Graph + adjacency tensor                     |
| `Top__Propositions__Prop_05.v`                  |  1413 | Tensors, NRT, DRT, DynamicNRT                |
| `Top__Propositions__Prop_10.v`                  |   917 | Directionality (uni / bi / multi / self)     |
| `Top__Propositions__ClockHierarchyCoherence.v`  |  1552 | Clock readings, tick algebra, hierarchies    |
| `Top__Cubical__Interval.v`                      |   456 | `I_R`, meet/join/neg, n-interval             |
| `Top__Cubical__PathType.v`                      |   502 | `RChain`, lift through extensions            |
| `Top__Cubical__NCube.v`                         |   751 | `RCube n U`, canonical fillers               |
| `Top__Cubical__Univalence.v`                    |   520 | `rel_ext_eq`, `RId`, transport               |
| `Top__Cubical__JRule.v`                         |   652 | `relational_J_full`, funext, 2-category      |
| `Top__Cubical__KanCanonical.v`                  |   499 | Canonical Kan filler, uniqueness             |
| `Top__Cubical__RCTT.v`                          |   583 | Umbrella + capstone theorems                 |
| **Total**                                       | **25,487** |                                         |

---

## License & citation

This source is distributed under the **Apache License, Version 2.0** —
see the [`LICENSE`](LICENSE) and [`NOTICE`](NOTICE) files for the full text
and required attribution. Every source file carries an SPDX `Apache-2.0`
marker. © 2023–2026 Michael Fillippini.

The names **UCF/GUTT**, **GUTT-L**, **LANTOSE**, **NRTML**, **RCTT**, and
**Relational Existence** are trademarks of Michael Fillippini; the Apache
2.0 license grants no rights in these trademarks. See [`TRADEMARKS.md`](TRADEMARKS.md)
for the permitted-use policy. Release verification, signing, and the
SHA-256 / GPG-signature procedure are documented in [`RELEASING.md`](RELEASING.md);
academic citation metadata is in [`CITATION.cff`](CITATION.cff).

For framework background, see <https://relationalexistence.com> and the
public GitHub mirror at <https://github.com/relationalexistence/UCF-GUTT>.

If you reference this library in academic work, please cite as:

> Fillippini, M. (2026). *UCF/GUTT Coq Library — Public Core, v2.0.0.*
> Zero-axiom Coq formalization of relational ontology, 30 files / 25,487
> lines / 1,230 theorems & lemmas, verified under Coq 8.18.
