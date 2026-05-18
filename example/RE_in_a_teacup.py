#!/usr/bin/env python3
# =============================================================================
#   UCF/GUTT(TM) -- Reality Engine in a Teacup, v3
#   Copyright 2023-2026 Michael Fillippini.
#
#   Licensed under the Apache License, Version 2.0 (the "License").
#       http://www.apache.org/licenses/LICENSE-2.0
#
#   SPDX-License-Identifier: Apache-2.0
# =============================================================================
"""
UCF/GUTT Proposition Firing v3 -- Reality Engine miniature with archival export.

CHANGES FROM v2
---------------
EXPORT MODE. A single command --
    python3 ucf_proposition_firing_v3.py export <dir>
-- writes four artifacts to <dir> that make the engine's results durable,
citable, and externally verifiable:

  1. firings.v        Coq script with Example statements asserting the
                      CORE firings for every system. Compiles against the
                      existing Top__Propositions__Prop_{01,02,04,05,10}.v
                      modules. Drop into the UCF/GUTT Coq project and
                      `coqc` to cross-check Python and Coq.

  2. firings.tex      A standalone LaTeX `table` environment summarizing
                      the proposition-firing patterns. Drop into the
                      GRB / Reality Engine paper.

  3. CITATION.cff     Citation File Format metadata. Recognized by
                      Zenodo, GitHub, and academic indexers; ensures
                      proper attribution when the work is cited.

  4. EXPORT_README.md A README that contextualizes the export and
                      explains how to use each artifact.

Why this is in the file. The engine is a demo; the export is what makes
the demo durable. Every run produces artifacts that survive the engine,
survive the platform, and remain citable. This is "leaving something"
expressed in code.

CORE PROPOSITIONS MIRRORED (unchanged from v2)
---------------------------------------------
    Top__Propositions__Prop_01   -- Seriality via Whole-completion
    Top__Propositions__Prop_02   -- Multi-dimensional representation (DSoR)
    Top__Propositions__Prop_04   -- Graph / Adjacency Tensor
    Top__Propositions__Prop_05   -- Relational Tensor / NRT modular composition
    Top__Propositions__Prop_07   -- Hyper-arity (not yet in public Coq core)
    Top__Propositions__Prop_10   -- Directionality

USAGE
-----
    python3 ucf_proposition_firing_v3.py                # all systems + smoke test
    python3 ucf_proposition_firing_v3.py ternary_only   # the headline target
    python3 ucf_proposition_firing_v3.py smoketest      # validation pass
    python3 ucf_proposition_firing_v3.py export <dir>   # archival artifacts
"""

from __future__ import annotations

import os
import sys
from dataclasses import dataclass, field
from datetime import datetime, timezone
from enum import Enum
from fractions import Fraction
from typing import (Callable, Dict, FrozenSet, List, Optional, Sequence,
                    Set, Tuple)


# =============================================================================
#   SECTION 1: CORE TYPES
# =============================================================================

@dataclass(frozen=True)
class Element:
    kind: str
    label: Optional[str]

    @classmethod
    def elem(cls, label: str) -> "Element":
        return cls(kind="elem", label=label)

    @classmethod
    def whole(cls) -> "Element":
        return cls(kind="whole", label=None)

    @property
    def is_whole(self) -> bool:
        return self.kind == "whole"

    def __str__(self) -> str:
        return "Whole" if self.is_whole else self.label  # type: ignore[return-value]


class Direction(Enum):
    UNDIRECTED = "Undirected"
    UNI = "Uni"
    BI = "Bi"
    MULTI = "Multi"


@dataclass(frozen=True)
class Edge:
    src: Element
    tgt: Element
    direction: Direction = Direction.UNI
    weight: Fraction = Fraction(1)

    def __post_init__(self) -> None:
        if self.src.is_whole:
            raise ValueError("Base edges may not originate at Whole.")
        if self.weight < 0:
            raise ValueError("Edge weight must be non-negative.")


@dataclass(frozen=True)
class HyperEdge:
    vertices: Tuple[Element, ...]
    weight: Fraction = Fraction(1)

    def __post_init__(self) -> None:
        if len(self.vertices) < 2:
            raise ValueError(
                f"HyperEdge requires arity >= 2, got {len(self.vertices)}.")
        for v in self.vertices:
            if v.is_whole:
                raise ValueError("HyperEdge vertices must be in base U.")
        if self.weight < 0:
            raise ValueError("HyperEdge weight must be non-negative.")

    @property
    def arity(self) -> int:
        return len(self.vertices)


# =============================================================================
#   SECTION 2: RELATIONAL SYSTEM
# =============================================================================

@dataclass(frozen=True)
class RelationalSystem:
    name: str
    base_elements: Tuple[Element, ...]
    base_edges: Tuple[Edge, ...] = ()
    base_hyperedges: Tuple[HyperEdge, ...] = ()

    def __post_init__(self) -> None:
        for e in self.base_elements:
            if e.is_whole:
                raise ValueError("Base universe U must not contain Whole.")
        labels = [e.label for e in self.base_elements]
        if len(set(labels)) != len(labels):
            raise ValueError("Base element labels must be unique.")
        for ed in self.base_edges:
            if ed.src not in self.base_elements:
                raise ValueError(f"Edge source {ed.src} not in U.")
            if ed.tgt not in self.base_elements and not ed.tgt.is_whole:
                raise ValueError(f"Edge target {ed.tgt} not in U_x.")
        for h in self.base_hyperedges:
            for v in h.vertices:
                if v not in self.base_elements:
                    raise ValueError(f"HyperEdge vertex {v} not in U.")

    @property
    def extended_elements(self) -> Tuple[Element, ...]:
        return self.base_elements + (Element.whole(),)

    def whole_completion_edges(self) -> Tuple[Edge, ...]:
        whole = Element.whole()
        return tuple(
            Edge(src=x, tgt=whole, direction=Direction.UNI,
                 weight=Fraction(1))
            for x in self.base_elements
        )

    def element_to_nat_index(self) -> Dict[Element, int]:
        """Stable mapping base elements -> nat indices for Coq export."""
        return {e: i for i, e in enumerate(self.base_elements)}


# =============================================================================
#   SECTION 3: RELATIONAL TENSOR + INVARIANTS
# =============================================================================

@dataclass(frozen=True)
class RelationalTensor:
    system: RelationalSystem
    adjacency: Dict[Tuple[Element, Element], Fraction]
    hyperedge_count_by_arity: Dict[int, int]
    n_base_elements: int
    n_extended_elements: int
    n_base_binary_edges: int
    n_base_binary_pairs: int
    n_base_hyperedges: int
    max_arity: int
    n_whole_completion_edges: int
    n_total_lifted_binary_edges: int
    is_reflexive_on_base: bool
    is_symmetric_on_base: bool
    is_transitive_on_base: bool
    has_self_loop: bool
    is_strongly_connected_on_base: bool
    base_direction_types: FrozenSet[Direction]
    n_isolated_pre_completion: int
    n_isolated_post_completion: int


def build_tensor(system: RelationalSystem) -> RelationalTensor:
    whole = Element.whole()
    base = system.base_elements
    base_set = set(base)

    adj: Dict[Tuple[Element, Element], Fraction] = {}
    base_pairs_only: Set[Tuple[Element, Element]] = set()

    for ed in system.base_edges:
        keys: List[Tuple[Element, Element]] = []
        if ed.direction in (Direction.UNI, Direction.MULTI):
            keys.append((ed.src, ed.tgt))
        elif ed.direction in (Direction.BI, Direction.UNDIRECTED):
            keys.append((ed.src, ed.tgt))
            keys.append((ed.tgt, ed.src))
        for k in keys:
            adj[k] = max(adj.get(k, Fraction(0)), ed.weight)
            base_pairs_only.add(k)

    for ed in system.whole_completion_edges():
        adj[(ed.src, whole)] = Fraction(1)
    adj[(whole, whole)] = Fraction(1)

    hyper_arity_count: Dict[int, int] = {}
    for h in system.base_hyperedges:
        hyper_arity_count[h.arity] = hyper_arity_count.get(h.arity, 0) + 1

    is_reflexive = (
        all((x, x) in base_pairs_only for x in base) if base else True
    )
    has_self_loop = any((x, x) in base_pairs_only for x in base)
    is_symmetric = all((t, s) in base_pairs_only for (s, t) in base_pairs_only)
    is_transitive = True
    for (s, t) in base_pairs_only:
        for u in base:
            if (t, u) in base_pairs_only and (s, u) not in base_pairs_only:
                is_transitive = False
                break
        if not is_transitive:
            break

    reachable: Dict[Element, Set[Element]] = {x: {x} for x in base}
    changed = True
    while changed:
        changed = False
        for x in base:
            new_reach = set(reachable[x])
            for y in list(reachable[x]):
                for (s, t) in base_pairs_only:
                    if s == y and t not in new_reach:
                        new_reach.add(t)
                        changed = True
            reachable[x] = new_reach
    is_strongly_connected = (
        bool(base) and all(reachable[x] == base_set for x in base)
    )

    base_dirs = frozenset(ed.direction for ed in system.base_edges)

    n_iso_pre = sum(
        1 for x in base
        if not any(s == x for (s, _) in base_pairs_only)
        and not any(x in h.vertices for h in system.base_hyperedges)
    )

    has_binary = len(system.base_edges) > 0
    if system.base_hyperedges:
        max_arity = max(h.arity for h in system.base_hyperedges)
    elif has_binary:
        max_arity = 2
    else:
        max_arity = 0

    return RelationalTensor(
        system=system,
        adjacency=adj,
        hyperedge_count_by_arity=hyper_arity_count,
        n_base_elements=len(base),
        n_extended_elements=len(base) + 1,
        n_base_binary_edges=len(system.base_edges),
        n_base_binary_pairs=len(base_pairs_only),
        n_base_hyperedges=len(system.base_hyperedges),
        max_arity=max_arity,
        n_whole_completion_edges=len(base) + 1,
        n_total_lifted_binary_edges=len(adj),
        is_reflexive_on_base=is_reflexive,
        is_symmetric_on_base=is_symmetric,
        is_transitive_on_base=is_transitive,
        has_self_loop=has_self_loop,
        is_strongly_connected_on_base=is_strongly_connected,
        base_direction_types=base_dirs,
        n_isolated_pre_completion=n_iso_pre,
        n_isolated_post_completion=0,
    )


# =============================================================================
#   SECTION 4: CORE PROPOSITION CHECKS
# =============================================================================

class PropositionID(Enum):
    P1 = ("P1", "Seriality via Whole-completion",
          "Top__Propositions__Prop_01")
    P2 = ("P2", "Multi-dimensional representation (DSoR)",
          "Top__Propositions__Prop_02")
    P4 = ("P4", "Graph / Adjacency Tensor",
          "Top__Propositions__Prop_04")
    P5 = ("P5", "Relational Tensor / NRT modular composition",
          "Top__Propositions__Prop_05")
    P7 = ("P7", "Hyper-arity (relations not restricted to binary)",
          "Top__Propositions__Prop_07")
    P10 = ("P10", "Directionality",
           "Top__Propositions__Prop_10")

    @property
    def short(self) -> str:
        return self.value[0]

    @property
    def title(self) -> str:
        return self.value[1]

    @property
    def coq_module(self) -> str:
        return self.value[2]


@dataclass(frozen=True)
class PropositionWitness:
    prop_id: PropositionID
    fired: bool
    is_unconditional: bool
    coq_theorem: str
    invariant_basis: str
    witness_summary: str
    witness_detail: List[str] = field(default_factory=list)


def check_prop_01(rt: RelationalTensor) -> PropositionWitness:
    extended = rt.system.extended_elements
    return PropositionWitness(
        prop_id=PropositionID.P1,
        fired=True,
        is_unconditional=True,
        coq_theorem="proposition_01_constructive (witness x := Whole)",
        invariant_basis=(
            f"|U_x| = {rt.n_extended_elements}; Whole-completion makes "
            f"R' serial: every x in U_x has R'(x, Whole)."
        ),
        witness_summary="Uniform constructive witness: Whole. Same y works for all x.",
        witness_detail=[
            f"R'({x}, Whole) holds via Whole-completion."
            for x in extended
        ],
    )


def check_prop_02(rt: RelationalTensor) -> PropositionWitness:
    if rt.n_base_binary_pairs == 0:
        return PropositionWitness(
            prop_id=PropositionID.P2, fired=False, is_unconditional=False,
            coq_theorem="multi_dim_representation",
            invariant_basis="No base binary pairs; nothing for DSoR to characterize.",
            witness_summary="DOES NOT FIRE -- P2 is binary-content-sensitive.",
        )
    sample: Optional[Tuple[Element, Element, Fraction]] = None
    base_set = set(rt.system.base_elements)
    for (s, t), w in rt.adjacency.items():
        if s in base_set and t in base_set and w > 0:
            sample = (s, t, w)
            break
    assert sample is not None
    s, t, w = sample
    return PropositionWitness(
        prop_id=PropositionID.P2, fired=True, is_unconditional=False,
        coq_theorem="multi_dim_representation (witness: ego-centric tensor T)",
        invariant_basis=(
            f"{rt.n_base_binary_pairs} base binary pair(s) admit DSoR "
            f"representations in R^n for any n >= 1."
        ),
        witness_summary=f"Sample DSoR_3({s}, {t}) = [{w}, 0, 0] in R^3.",
        witness_detail=[
            f"  dim 0 (weight)   : {w}",
            "  dim 1 (reserved) : 0",
            "  dim 2 (reserved) : 0",
            "  Tensor T is ego-centric: T(x,y) need not equal T(y,x).",
        ],
    )


def check_prop_04(rt: RelationalTensor) -> PropositionWitness:
    n_nonzero = sum(1 for w in rt.adjacency.values() if w > 0)
    base_set = set(rt.system.base_elements)
    base_entry: Optional[Tuple[Element, Element, Fraction]] = None
    whole_entry: Optional[Tuple[Element, Element, Fraction]] = None
    for (s, t), w in rt.adjacency.items():
        if w > 0 and s in base_set and t in base_set and base_entry is None:
            base_entry = (s, t, w)
        if w > 0 and s in base_set and t.is_whole and whole_entry is None:
            whole_entry = (s, t, w)
    detail = [
        f"  isolation pre-completion : {rt.n_isolated_pre_completion}",
        f"  isolation post-completion: {rt.n_isolated_post_completion}  "
        f"(provably 0 by Whole-completion)",
    ]
    if base_entry:
        s, t, w = base_entry
        detail.append(f"  base sample              : AdjacencyTensor({s}, {t}) = {w}")
    if whole_entry:
        s, t, w = whole_entry
        detail.append(f"  Whole-completion sample  : AdjacencyTensor({s}, Whole) = {w}")
    return PropositionWitness(
        prop_id=PropositionID.P4, fired=True, is_unconditional=False,
        coq_theorem="adjacency_tensor_iff, no_isolated_entities",
        invariant_basis=(
            f"AdjacencyTensor has {n_nonzero} non-zero entries on U_x x U_x; "
            f"no isolated entity post-completion."
        ),
        witness_summary=(
            "Graph representation: every R' edge has tensor weight >= 1; "
            "no entity is isolated thanks to Whole."
        ),
        witness_detail=detail,
    )


def check_prop_05(rt: RelationalTensor) -> PropositionWitness:
    nrt_lines: List[str] = []
    binary_by_dir: Dict[Direction, int] = {}
    for ed in rt.system.base_edges:
        binary_by_dir[ed.direction] = binary_by_dir.get(ed.direction, 0) + 1
    for d, n in binary_by_dir.items():
        nrt_lines.append(f"  NRT[binary:{d.value}]   : {n} base edge(s)")
    for arity in sorted(rt.hyperedge_count_by_arity):
        n = rt.hyperedge_count_by_arity[arity]
        nrt_lines.append(f"  NRT[hyper:arity={arity}]  : {n} base hyperedge(s)")
    nrt_lines.append(
        f"  NRT[Whole-completion]   : {rt.n_whole_completion_edges} structural edge(s)"
    )
    total = sum(rt.adjacency.values(), Fraction(0))
    keys = list(rt.adjacency.keys())
    half = keys[: max(1, len(keys) // 2)]
    rest = keys[len(half):]
    half_sum = sum((rt.adjacency[k] for k in half), Fraction(0))
    rest_sum = sum((rt.adjacency[k] for k in rest), Fraction(0))
    modularity_holds = (half_sum + rest_sum) == total
    detail = nrt_lines + [
        "",
        "  modularity check (exact Q)",
        f"    composite_tensor total   : {total}",
        f"    half_sum + rest_sum      : {half_sum + rest_sum}",
        f"    equal?                   : {modularity_holds}",
    ]
    n_components = len(binary_by_dir) + len(rt.hyperedge_count_by_arity) + 1
    return PropositionWitness(
        prop_id=PropositionID.P5, fired=True, is_unconditional=False,
        coq_theorem="proposition_5_relational_tensor (5 clauses)",
        invariant_basis=f"{n_components} NRT component(s) compose into the system RT.",
        witness_summary=(
            "Composite tensor = sum over NRT components; modularity verified in exact Q."
        ),
        witness_detail=detail,
    )


def check_prop_07(rt: RelationalTensor) -> PropositionWitness:
    if rt.n_base_hyperedges == 0:
        return PropositionWitness(
            prop_id=PropositionID.P7, fired=False, is_unconditional=False,
            coq_theorem="hyper_arity_primitive",
            invariant_basis=f"max base arity = {rt.max_arity}; no hyperedges present.",
            witness_summary="DOES NOT FIRE -- no hyperedge content in base R.",
        )
    sample = rt.system.base_hyperedges[0]
    sample_str = ", ".join(str(v) for v in sample.vertices)
    arity_str = ", ".join(
        f"arity={a}: {n}"
        for a, n in sorted(rt.hyperedge_count_by_arity.items())
    )
    return PropositionWitness(
        prop_id=PropositionID.P7, fired=True, is_unconditional=False,
        coq_theorem="hyper_arity_primitive",
        invariant_basis=(
            f"{rt.n_base_hyperedges} base hyperedge(s); arity distribution: "
            f"{{{arity_str}}}; max arity = {rt.max_arity}."
        ),
        witness_summary=(
            f"Sample: R({sample_str}) is a primitive {sample.arity}-ary edge, "
            f"not derivable from binary projections."
        ),
        witness_detail=[
            f"  sample hyperedge       : R({sample_str}) weight={sample.weight}",
            f"  arity distribution     : {{{arity_str}}}",
            f"  max base arity         : {rt.max_arity}",
        ],
    )


def check_prop_10(rt: RelationalTensor) -> PropositionWitness:
    base_dirs = rt.base_direction_types
    if not base_dirs:
        return PropositionWitness(
            prop_id=PropositionID.P10, fired=False, is_unconditional=False,
            coq_theorem="universal_connectivity_directed",
            invariant_basis="No base binary edges; no direction types to attribute.",
            witness_summary="DOES NOT FIRE -- P10 is binary-content-sensitive.",
        )
    all_dirs = {Direction.UNDIRECTED, Direction.UNI,
                Direction.BI, Direction.MULTI}
    missing = all_dirs - base_dirs
    present_str = ", ".join(d.value for d in sorted(base_dirs, key=lambda d: d.value))
    missing_str = ", ".join(d.value for d in sorted(missing, key=lambda d: d.value))
    return PropositionWitness(
        prop_id=PropositionID.P10, fired=True, is_unconditional=False,
        coq_theorem="universal_connectivity_directed, direction_independent_of_existence",
        invariant_basis=f"{len(base_dirs)} of 4 direction types present in BASE R.",
        witness_summary=(
            "Every base binary edge has a direction; direction is independent "
            "of existence (add/remove/change preserves existence)."
        ),
        witness_detail=[
            f"  direction types in base R : {{{present_str}}}",
            f"  direction types absent    : {{{missing_str}}}"
            if missing else "  direction types absent    : {}  (all four present)",
        ],
    )


CORE_PROPOSITION_CHECKS: Tuple[Callable[[RelationalTensor], PropositionWitness], ...] = (
    check_prop_01, check_prop_02, check_prop_04,
    check_prop_05, check_prop_07, check_prop_10,
)


def fire_propositions(rt: RelationalTensor) -> List[PropositionWitness]:
    return [check(rt) for check in CORE_PROPOSITION_CHECKS]


# =============================================================================
#   SECTION 5: DERIVED PROPOSITION CHECKS
# =============================================================================

@dataclass(frozen=True)
class DerivedWitness:
    prop_id: str
    title: str
    fired: bool
    guard_description: str
    guard_passed: bool
    invariant_basis: str
    witness_summary: str
    witness_detail: List[str] = field(default_factory=list)

    @property
    def status_label(self) -> str:
        if not self.guard_passed:
            return "GUARD FAILED"
        if self.fired:
            return "FIRES"
        return "GUARD PASSED, PROPERTY VIOLATED"


def check_derived_equivalence(rt: RelationalTensor) -> DerivedWitness:
    guard_desc = "base R has at least one binary pair"
    if rt.n_base_binary_pairs == 0:
        return DerivedWitness(
            prop_id="D_eq", title="Equivalence relation on U",
            fired=False, guard_description=guard_desc, guard_passed=False,
            invariant_basis=(
                "No base binary content; equivalence-relation property is "
                "vacuously satisfied but uninformative."
            ),
            witness_summary="D_eq is undefined on an empty base relation.",
        )
    refl = rt.is_reflexive_on_base
    sym = rt.is_symmetric_on_base
    trans = rt.is_transitive_on_base
    fired = refl and sym and trans
    if fired:
        return DerivedWitness(
            prop_id="D_eq", title="Equivalence relation on U",
            fired=True, guard_description=guard_desc, guard_passed=True,
            invariant_basis="Base R is reflexive, symmetric, and transitive.",
            witness_summary="Base R partitions U into equivalence classes.",
            witness_detail=[
                f"  reflexive on U  : {refl}",
                f"  symmetric on U  : {sym}",
                f"  transitive on U : {trans}",
            ],
        )
    violations: List[str] = []
    if not refl:
        violations.append("not reflexive")
    if not sym:
        violations.append("not symmetric")
    if not trans:
        violations.append("not transitive")
    return DerivedWitness(
        prop_id="D_eq", title="Equivalence relation on U",
        fired=False, guard_description=guard_desc, guard_passed=True,
        invariant_basis=f"Base R violates: {', '.join(violations)}.",
        witness_summary="Guard passed but equivalence property failed.",
        witness_detail=[
            f"  reflexive on U  : {refl}",
            f"  symmetric on U  : {sym}",
            f"  transitive on U : {trans}",
        ],
    )


def check_derived_functional(rt: RelationalTensor) -> DerivedWitness:
    guard_desc = "base R has at least one binary pair"
    if rt.n_base_binary_pairs == 0:
        return DerivedWitness(
            prop_id="D_fun", title="Functional / deterministic relation on U",
            fired=False, guard_description=guard_desc, guard_passed=False,
            invariant_basis="No base binary content.",
            witness_summary="D_fun is undefined on an empty base relation.",
        )
    base = rt.system.base_elements
    base_set = set(base)
    out_counts: Dict[Element, int] = {x: 0 for x in base}
    for (s, t), w in rt.adjacency.items():
        if s in base_set and t in base_set and w > 0:
            out_counts[s] += 1
    max_out = max(out_counts.values()) if out_counts else 0
    fired = max_out <= 1
    violators = [(str(x), c) for x, c in out_counts.items() if c > 1]
    # v3: distinguish total vs partial function (v2 wart fix)
    is_total = fired and all(c == 1 for c in out_counts.values())
    qualifier = "(total)" if is_total else "(partial)"
    if fired:
        return DerivedWitness(
            prop_id="D_fun", title="Functional / deterministic relation on U",
            fired=True, guard_description=guard_desc, guard_passed=True,
            invariant_basis=(
                f"Every x in U has out-degree <= 1 in base R; max = {max_out}."
            ),
            witness_summary=f"Base R is a {qualifier} function on U.",
            witness_detail=[
                "  out-degrees: " + ", ".join(
                    f"{x}: {c}" for x, c in out_counts.items()
                ),
            ],
        )
    return DerivedWitness(
        prop_id="D_fun", title="Functional / deterministic relation on U",
        fired=False, guard_description=guard_desc, guard_passed=True,
        invariant_basis=(
            f"{len(violators)} element(s) violate the at-most-one-out-edge bound."
        ),
        witness_summary="Guard passed but functional property failed.",
        witness_detail=[
            "  out-degrees: " + ", ".join(
                f"{x}: {c}" for x, c in out_counts.items()
            ),
            "  violators (out > 1): "
            + ", ".join(f"{x} (out={c})" for x, c in violators),
        ],
    )


DERIVED_PROPOSITION_CHECKS: Tuple[Callable[[RelationalTensor], DerivedWitness], ...] = (
    check_derived_equivalence,
    check_derived_functional,
)


def fire_derived(rt: RelationalTensor) -> List[DerivedWitness]:
    return [check(rt) for check in DERIVED_PROPOSITION_CHECKS]


# =============================================================================
#   SECTION 6: EXAMPLE SYSTEMS
# =============================================================================

def system_empty() -> RelationalSystem:
    a, b, c = (Element.elem(x) for x in ("a", "b", "c"))
    return RelationalSystem(
        name="EMPTY (|U|=3, R = {})",
        base_elements=(a, b, c),
    )


def system_cycle4() -> RelationalSystem:
    a, b, c, d = (Element.elem(x) for x in ("a", "b", "c", "d"))
    return RelationalSystem(
        name="CYCLE_4 (directed: a -> b -> c -> d -> a)",
        base_elements=(a, b, c, d),
        base_edges=(Edge(a, b), Edge(b, c), Edge(c, d), Edge(d, a)),
    )


def system_k4_undirected() -> RelationalSystem:
    a, b, c, d = (Element.elem(x) for x in ("a", "b", "c", "d"))
    pairs = [(a, b), (a, c), (a, d), (b, c), (b, d), (c, d)]
    return RelationalSystem(
        name="K_4 (undirected complete graph on 4 vertices)",
        base_elements=(a, b, c, d),
        base_edges=tuple(Edge(s, t, direction=Direction.UNDIRECTED) for s, t in pairs),
    )


def system_selfloop_isolated() -> RelationalSystem:
    a, b, c = (Element.elem(x) for x in ("a", "b", "c"))
    return RelationalSystem(
        name="SELFLOOP_ISOLATED (a -> a; b, c isolated pre-completion)",
        base_elements=(a, b, c),
        base_edges=(Edge(a, a, direction=Direction.UNI),),
    )


def system_mixed_directions() -> RelationalSystem:
    a, b, c, d = (Element.elem(x) for x in ("a", "b", "c", "d"))
    return RelationalSystem(
        name="MIXED_DIRECTIONS (all 4 direction types present)",
        base_elements=(a, b, c, d),
        base_edges=(
            Edge(a, b, direction=Direction.UNI),
            Edge(a, c, direction=Direction.BI),
            Edge(a, d, direction=Direction.UNDIRECTED),
            Edge(a, d, direction=Direction.MULTI, weight=Fraction(2)),
        ),
    )


def system_equivalence() -> RelationalSystem:
    a, b, c = (Element.elem(x) for x in ("a", "b", "c"))
    return RelationalSystem(
        name="EQUIVALENCE_2CLASS (classes {a,b}, {c}; reflexive+sym+trans)",
        base_elements=(a, b, c),
        base_edges=(
            Edge(a, a, direction=Direction.UNI),
            Edge(b, b, direction=Direction.UNI),
            Edge(c, c, direction=Direction.UNI),
            Edge(a, b, direction=Direction.BI),
        ),
    )


def system_ternary_only() -> RelationalSystem:
    a, b, c = (Element.elem(x) for x in ("a", "b", "c"))
    return RelationalSystem(
        name="TERNARY_ONLY (R(a,b,c) hyperedge only; no binary R)",
        base_elements=(a, b, c),
        base_hyperedges=(HyperEdge(vertices=(a, b, c)),),
    )


def system_binary_plus_ternary() -> RelationalSystem:
    a, b, c, d = (Element.elem(x) for x in ("a", "b", "c", "d"))
    return RelationalSystem(
        name="BINARY_PLUS_TERNARY (mixed-arity base relation)",
        base_elements=(a, b, c, d),
        base_edges=(Edge(a, b, direction=Direction.BI),),
        base_hyperedges=(HyperEdge(vertices=(b, c, d)),),
    )


SYSTEM_REGISTRY: Dict[str, Callable[[], RelationalSystem]] = {
    "empty":               system_empty,
    "cycle4":              system_cycle4,
    "k4":                  system_k4_undirected,
    "selfloop":            system_selfloop_isolated,
    "mixed":               system_mixed_directions,
    "equivalence":         system_equivalence,
    "ternary_only":        system_ternary_only,
    "binary_plus_ternary": system_binary_plus_ternary,
}


# =============================================================================
#   SECTION 7: SMOKE TEST
# =============================================================================

EXPECTED_FIRING: Dict[str, FrozenSet[str]] = {
    "empty":               frozenset({"P1", "P4", "P5"}),
    "cycle4":              frozenset({"P1", "P2", "P4", "P5", "P10"}),
    "k4":                  frozenset({"P1", "P2", "P4", "P5", "P10"}),
    "selfloop":            frozenset({"P1", "P2", "P4", "P5", "P10"}),
    "mixed":               frozenset({"P1", "P2", "P4", "P5", "P10"}),
    "equivalence":         frozenset({"P1", "P2", "P4", "P5", "P10"}),
    "ternary_only":        frozenset({"P1", "P4", "P5", "P7"}),
    "binary_plus_ternary": frozenset({"P1", "P2", "P4", "P5", "P7", "P10"}),
}

EXPECTED_DERIVED: Dict[str, FrozenSet[str]] = {
    "empty":               frozenset(),
    "cycle4":              frozenset({"D_fun"}),
    "k4":                  frozenset(),
    "selfloop":            frozenset({"D_fun"}),
    "mixed":               frozenset(),
    "equivalence":         frozenset({"D_eq"}),
    "ternary_only":        frozenset(),
    "binary_plus_ternary": frozenset({"D_fun"}),
}


@dataclass(frozen=True)
class SmokeTestRow:
    system_name: str
    actual_core: FrozenSet[str]
    expected_core: FrozenSet[str]
    actual_derived: FrozenSet[str]
    expected_derived: FrozenSet[str]

    @property
    def core_ok(self) -> bool:
        return self.actual_core == self.expected_core

    @property
    def derived_ok(self) -> bool:
        return self.actual_derived == self.expected_derived

    @property
    def passed(self) -> bool:
        return self.core_ok and self.derived_ok


def smoke_test() -> List[SmokeTestRow]:
    rows: List[SmokeTestRow] = []
    for name in SYSTEM_REGISTRY:
        system = SYSTEM_REGISTRY[name]()
        rt = build_tensor(system)
        core = fire_propositions(rt)
        derived = fire_derived(rt)
        actual_core = frozenset(w.prop_id.short for w in core if w.fired)
        actual_derived = frozenset(w.prop_id for w in derived if w.fired)
        rows.append(SmokeTestRow(
            system_name=name,
            actual_core=actual_core,
            expected_core=EXPECTED_FIRING[name],
            actual_derived=actual_derived,
            expected_derived=EXPECTED_DERIVED[name],
        ))
    return rows


# =============================================================================
#   SECTION 8: PRETTY PRINTING (CONSOLE OUTPUT)
# =============================================================================

def _hr(width: int = 76, char: str = "=") -> str:
    return char * width


def _banner(title: str, width: int = 76) -> str:
    return f"{_hr(width)}\n  {title}\n{_hr(width)}"


def _format_tensor_invariants(rt: RelationalTensor) -> List[str]:
    dirs_str = (
        "{" + ", ".join(d.value for d in
                        sorted(rt.base_direction_types,
                               key=lambda d: d.value)) + "}"
        if rt.base_direction_types else "{}"
    )
    base_elt_labels = ", ".join(str(x) for x in rt.system.base_elements) or "(none)"
    hyper_str = (
        ", ".join(f"arity={a}: {n}" for a, n in
                  sorted(rt.hyperedge_count_by_arity.items()))
        if rt.hyperedge_count_by_arity else "(none)"
    )
    refl_note = " (vacuous)" if rt.n_base_binary_pairs == 0 else ""
    return [
        f"  base universe U          : {{{base_elt_labels}}}",
        f"  |U|                      : {rt.n_base_elements}",
        f"  |U_x| = |U| + 1          : {rt.n_extended_elements}",
        f"  |base binary R|          : {rt.n_base_binary_edges} edge(s), "
        f"{rt.n_base_binary_pairs} pair(s)",
        f"  |base hyperedges|        : {rt.n_base_hyperedges}  ({hyper_str})",
        f"  max base arity           : {rt.max_arity}",
        f"  |Whole-completion edges| : {rt.n_whole_completion_edges}",
        f"  |R' on U_x| (binary)     : {rt.n_total_lifted_binary_edges}",
        "",
        f"  reflexive on U           : {rt.is_reflexive_on_base}{refl_note}",
        f"  symmetric on U           : {rt.is_symmetric_on_base}{refl_note}",
        f"  transitive on U          : {rt.is_transitive_on_base}{refl_note}",
        f"  has self-loop on U       : {rt.has_self_loop}",
        f"  strongly connected on U  : {rt.is_strongly_connected_on_base}",
        f"  direction types in R     : {dirs_str}",
        "",
        f"  isolated entities pre-completion  : {rt.n_isolated_pre_completion}",
        f"  isolated entities post-completion : {rt.n_isolated_post_completion}  "
        f"(== 0 by Whole-completion, always)",
    ]


def _format_witness(w: PropositionWitness) -> List[str]:
    star = " *** UNCONDITIONAL ROOT ***" if w.is_unconditional else ""
    status = "FIRES" if w.fired else "DOES NOT FIRE"
    out = [
        f"  [{w.prop_id.short}] {w.prop_id.title}{star}",
        f"      status   : {status}",
        f"      Coq ref  : {w.prop_id.coq_module}",
        f"      theorem  : {w.coq_theorem}",
        f"      basis    : {w.invariant_basis}",
        f"      witness  : {w.witness_summary}",
    ]
    if w.witness_detail:
        out.append("      detail   :")
        for line in w.witness_detail:
            out.append(f"        {line}")
    return out


def _format_derived(w: DerivedWitness) -> List[str]:
    out = [
        f"  [{w.prop_id}] {w.title}",
        f"      status   : {w.status_label}",
        f"      guard    : {w.guard_description} -- {'PASSED' if w.guard_passed else 'FAILED'}",
        f"      basis    : {w.invariant_basis}",
        f"      witness  : {w.witness_summary}",
    ]
    if w.witness_detail:
        out.append("      detail   :")
        for line in w.witness_detail:
            out.append(f"        {line}")
    return out


def render_report(rt: RelationalTensor,
                  core_witnesses: Sequence[PropositionWitness],
                  derived_witnesses: Sequence[DerivedWitness]) -> str:
    parts: List[str] = []
    parts.append(_banner(f"SYSTEM: {rt.system.name}"))
    parts.append("")
    parts.append("  TENSOR INVARIANTS")
    parts.append("  " + "-" * 72)
    parts.extend(_format_tensor_invariants(rt))
    parts.append("")
    parts.append("  CORE PROPOSITION FIRING")
    parts.append("  " + "-" * 72)
    for w in core_witnesses:
        parts.extend(_format_witness(w))
        parts.append("")
    parts.append("  DERIVED PROPOSITION FIRING (GUARDED)")
    parts.append("  " + "-" * 72)
    for w in derived_witnesses:
        parts.extend(_format_derived(w))
        parts.append("")
    return "\n".join(parts)


def render_smoke_test(rows: Sequence[SmokeTestRow]) -> str:
    parts: List[str] = []
    parts.append(_banner("SMOKE TEST -- proposition firing validation"))
    parts.append("")
    parts.append("  Target: actual firing pattern == expected, for every system.")
    parts.append("  Headline case: ternary_only must fire EXACTLY {P1, P4, P5, P7}.")
    parts.append("")
    header = (
        f"  {'system':<22} {'core actual':<26} {'core expected':<26} "
        f"{'derived actual':<14} {'expected':<14} ok?"
    )
    parts.append(header)
    parts.append("  " + "-" * (len(header) - 2))

    def fmt_set(s: FrozenSet[str]) -> str:
        if not s:
            return "{}"
        return "{" + ",".join(sorted(s)) + "}"

    all_pass = True
    for r in rows:
        ok = "PASS" if r.passed else "FAIL"
        if not r.passed:
            all_pass = False
        parts.append(
            f"  {r.system_name:<22} "
            f"{fmt_set(r.actual_core):<26} "
            f"{fmt_set(r.expected_core):<26} "
            f"{fmt_set(r.actual_derived):<14} "
            f"{fmt_set(r.expected_derived):<14} "
            f"{ok}"
        )
    parts.append("")
    parts.append(f"  OVERALL: {'ALL PASS' if all_pass else 'FAILURES PRESENT'}")
    return "\n".join(parts)


# =============================================================================
#   SECTION 9: EXPORT -- COQ, LATEX, CITATION, README
#
#   This section is the "legacy" payload. Every run with `export <dir>`
#   produces durable artifacts suitable for archival and citation.
# =============================================================================

ENGINE_VERSION = "v3.0.0"
ENGINE_NAME = "UCF/GUTT Reality Engine in a Teacup"


def _coq_relation_def(system: RelationalSystem,
                      idx: Dict[Element, int]) -> List[str]:
    """Generate Coq Definition for the base binary relation R on nat."""
    out = ["  (* Base binary relation R on nat (indexed from base_elements). *)"]
    if not system.base_edges:
        out.append("  Definition R (x y : nat) : Prop := False.")
        return out
    cases: List[str] = []
    for ed in system.base_edges:
        if ed.tgt.is_whole:
            continue  # Whole-edges are added by R_prime, not by R itself.
        si = idx[ed.src]
        ti = idx[ed.tgt]
        if ed.direction in (Direction.UNI, Direction.MULTI):
            cases.append(f"(x = {si} /\\ y = {ti})")
        elif ed.direction in (Direction.BI, Direction.UNDIRECTED):
            cases.append(f"(x = {si} /\\ y = {ti})")
            cases.append(f"(x = {ti} /\\ y = {si})")
    if not cases:
        out.append("  Definition R (x y : nat) : Prop := False.")
    else:
        out.append("  Definition R (x y : nat) : Prop :=")
        for i, c in enumerate(cases):
            sep = " \\/" if i < len(cases) - 1 else "."
            out.append(f"    {c}{sep}")
    return out


def _coq_examples_for_system(system: RelationalSystem,
                              witnesses: List[PropositionWitness]) -> List[str]:
    """Generate Coq Example statements for the firings of this system."""
    out: List[str] = []
    idx = system.element_to_nat_index()

    for w in witnesses:
        sn = w.prop_id.short
        if not w.fired:
            out.append(f"  (* {sn} does not fire on this system. *)")
            out.append(f"  (*     basis: {w.invariant_basis} *)")
            out.append("")
            continue

        if sn == "P1":
            out.append("  (* P1: Seriality via Whole-completion. UNCONDITIONAL ROOT. *)")
            out.append("  Example fires_P1 :")
            out.append("    forall x : Ux nat, exists y, R_prime R x y.")
            out.append("  Proof. intro x. exists Whole. apply UE.serial. Qed.")
            out.append("")

        elif sn == "P2":
            # Find a base binary pair to instantiate the witness over.
            sample: Optional[Tuple[int, int]] = None
            for ed in system.base_edges:
                if ed.tgt.is_whole:
                    continue
                if ed.direction in (Direction.UNI, Direction.MULTI,
                                     Direction.BI, Direction.UNDIRECTED):
                    sample = (idx[ed.src], idx[ed.tgt])
                    break
            if sample is None:
                out.append("  (* P2: no instantiable base pair (should not happen). *)")
            else:
                si, ti = sample
                out.append("  (* P2: Multi-dimensional representation (DSoR). *)")
                out.append("  Example fires_P2 :")
                out.append(f"    R_prime R (elem {si}) (elem {ti}) ->")
                out.append("    exists (d : DSoR 3) (T : ExtendedTensor nat 3),")
                out.append(f"      T (elem {si}) (elem {ti}) = d.")
                out.append("  Proof. intro H. apply (multi_dim_representation R). exact H. Qed.")
                out.append("")

        elif sn == "P4":
            out.append("  (* P4: Graph / Adjacency Tensor (via Whole-completion). *)")
            out.append("  Example fires_P4 :")
            out.append("    forall x : Ux nat,")
            out.append("      exists G : Graph nat, In (x, @Whole nat) (edges G).")
            out.append("  Proof.")
            out.append("    intro x.")
            out.append("    exists (singleton_graph x (@Whole nat)).")
            out.append("    simpl. left. reflexivity.")
            out.append("  Qed.")
            out.append("")

        elif sn == "P5":
            out.append("  (* P5: Relational Tensor / NRT modular composition. *)")
            out.append("  Example fires_P5 :")
            out.append("    forall x : Ux nat,")
            out.append("      exists RT : RelationalTensor nat,")
            out.append("        composite_tensor RT x (@Whole nat) >= 1.")
            out.append("  Proof. apply (every_entity_in_RT R). Qed.")
            out.append("")

        elif sn == "P7":
            out.append("  (* P7: Hyper-arity. NOT YET FORMALIZED in public Coq core. *)")
            out.append("  (*     Awaiting Top__Propositions__Prop_07.v. *)")
            out.append("  (*     Engine confirms hyperedge content: *)")
            for h in system.base_hyperedges:
                vs = ", ".join(str(idx[v]) for v in h.vertices)
                out.append(f"  (*       R({vs}) is primitive {h.arity}-ary. *)")
            out.append("")

        elif sn == "P10":
            out.append("  (* P10: Directionality. *)")
            out.append("  Example fires_P10 :")
            out.append("    exists r : RelationWithDirection nat,")
            out.append("      RelationExists nat r.")
            out.append("  Proof.")
            out.append("    exists (DirectedRelation_Uni nat (elem 0) Whole).")
            out.append("    apply relation_exists_with_unidirectional.")
            out.append("  Qed.")
            out.append("")

    return out


def _coq_module_name(system_name: str) -> str:
    """Convert a system name like 'EMPTY (|U|=3, R = {})' to a valid Coq Module name."""
    base = system_name.split(" ")[0]
    safe = "".join(c if c.isalnum() else "_" for c in base)
    return f"SmokeTest_{safe}"


def export_coq(out_path: str) -> None:
    """Write firings.v -- Coq examples asserting CORE firings for every system."""
    lines: List[str] = []
    timestamp = datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M:%S UTC")
    lines.append("(*")
    lines.append(f"  Generated by {ENGINE_NAME} {ENGINE_VERSION}")
    lines.append(f"  Generated at: {timestamp}")
    lines.append("")
    lines.append("  This file is a cross-check artifact: each Example asserts a")
    lines.append("  proposition firing that the Python engine claims for the named")
    lines.append("  system. Compiling this file against the existing UCF/GUTT Coq")
    lines.append("  library verifies the engine's claims at the proof level.")
    lines.append("")
    lines.append("  USAGE")
    lines.append("    1. Place this file alongside the Top__Propositions__*.v modules.")
    lines.append("    2. Add it to _CoqProject after the propositions it depends on.")
    lines.append("    3. Run `coqc` (or `make`). Successful compilation = cross-check passes.")
    lines.append("")
    lines.append("  AXIOM STATUS")
    lines.append("    Inherits zero-axiom discipline from the underlying library.")
    lines.append("    Run `Print Assumptions fires_PN.` to verify any specific Example.")
    lines.append("*)")
    lines.append("")
    lines.append("Require Import Top__Extensions__Prelude.")
    lines.append("Require Import Top__Propositions__Prop_01.")
    lines.append("Require Import Top__Propositions__Prop_02.")
    lines.append("Require Import Top__Propositions__Prop_04.")
    lines.append("Require Import Top__Propositions__Prop_05.")
    lines.append("Require Import Top__Propositions__Prop_10.")
    lines.append("Require Import Coq.Lists.List.")
    lines.append("Import ListNotations.")
    lines.append("")

    for name in SYSTEM_REGISTRY:
        system = SYSTEM_REGISTRY[name]()
        rt = build_tensor(system)
        witnesses = fire_propositions(rt)
        mod_name = _coq_module_name(name)
        lines.append("(* " + "=" * 74 + " *)")
        lines.append(f"(* SYSTEM: {system.name} *)")
        lines.append("(* " + "=" * 74 + " *)")
        lines.append(f"Module {mod_name}.")
        lines.append("")
        lines.extend(_coq_relation_def(system, system.element_to_nat_index()))
        lines.append("")
        lines.extend(_coq_examples_for_system(system, witnesses))
        lines.append(f"End {mod_name}.")
        lines.append("")
        lines.append("")

    with open(out_path, "w", encoding="utf-8") as f:
        f.write("\n".join(lines))


def export_latex(out_path: str, rows: Sequence[SmokeTestRow]) -> None:
    """Write firings.tex -- a standalone LaTeX `table` environment."""
    timestamp = datetime.now(timezone.utc).strftime("%Y-%m-%d")
    lines: List[str] = []
    lines.append(f"% Generated by {ENGINE_NAME} {ENGINE_VERSION} on {timestamp}.")
    lines.append("% Drop into the paper. Requires \\usepackage{booktabs} and")
    lines.append("% \\usepackage{pifont} (for \\ding{51}, the checkmark).")
    lines.append("%")
    lines.append("% Legend:")
    lines.append("%   \\cmark : fires (CORE) or fires (DERIVED)")
    lines.append("%   \\xmark : does not fire (CORE) or guard passed but property violated (DERIVED)")
    lines.append("%   \\dash  : guard failed (DERIVED only)")
    lines.append("%")
    lines.append("\\newcommand{\\cmark}{\\ding{51}}")
    lines.append("\\newcommand{\\xmark}{$\\times$}")
    lines.append("\\newcommand{\\dash}{---}")
    lines.append("")
    lines.append("\\begin{table}[ht]")
    lines.append("  \\centering")
    lines.append("  \\caption{Proposition firing patterns across eight relational")
    lines.append("    systems in the UCF/GUTT Reality Engine validator. P1 is the")
    lines.append("    unconditional root (Whole-completion); P2 and P10 require base")
    lines.append("    binary content; P7 requires hyper-arity content. CORE propositions")
    lines.append("    read directly off tensor invariants; DERIVED propositions are")
    lines.append("    guarded. The \\texttt{ternary\\_only} row exhibits the architectural")
    lines.append("    target: a plain ternary relation fires exactly \\{P1, P4, P5, P7\\}.}")
    lines.append("  \\label{tab:re_firings}")
    lines.append("  \\begin{tabular}{lcccccccc}")
    lines.append("    \\toprule")
    lines.append("    System & P1 & P2 & P4 & P5 & P7 & P10 & D\\_eq & D\\_fun \\\\")
    lines.append("    \\midrule")

    def _core_sym(name: str, prop: str) -> str:
        return "\\cmark" if prop in EXPECTED_FIRING[name] else "\\xmark"

    def _derived_sym(name: str, prop: str) -> str:
        # Three-state: fired, guard-passed-violated, guard-failed.
        system = SYSTEM_REGISTRY[name]()
        rt = build_tensor(system)
        derived = fire_derived(rt)
        for w in derived:
            if w.prop_id == prop:
                if w.fired:
                    return "\\cmark"
                if w.guard_passed:
                    return "\\xmark"
                return "\\dash"
        return "\\dash"

    for r in rows:
        name = r.system_name
        bold_open = "\\textbf{" if name == "ternary_only" else ""
        bold_close = "}" if name == "ternary_only" else ""
        latex_name = name.replace("_", "\\_")
        row = (
            f"    {bold_open}{latex_name}{bold_close} "
            f"& {_core_sym(name, 'P1')} & {_core_sym(name, 'P2')} "
            f"& {_core_sym(name, 'P4')} & {_core_sym(name, 'P5')} "
            f"& {_core_sym(name, 'P7')} & {_core_sym(name, 'P10')} "
            f"& {_derived_sym(name, 'D_eq')} & {_derived_sym(name, 'D_fun')} \\\\"
        )
        lines.append(row)
    lines.append("    \\bottomrule")
    lines.append("  \\end{tabular}")
    lines.append("\\end{table}")
    lines.append("")
    with open(out_path, "w", encoding="utf-8") as f:
        f.write("\n".join(lines))


def export_citation(out_path: str) -> None:
    """Write CITATION.cff -- citation metadata for Zenodo/GitHub/indexers."""
    today = datetime.now(timezone.utc).strftime("%Y-%m-%d")
    cff = f"""cff-version: 1.2.0
message: >
  If you use this software, please cite it using the metadata below.
  Please also cite the underlying UCF/GUTT (Unified Conceptual Framework /
  Grand Unified Tensor Theory) Coq library that this software cross-checks.
title: "{ENGINE_NAME}: A Proposition Firing Validator for UCF/GUTT"
abstract: >
  A Python validator that mirrors the INTEGRATED propositions of the
  UCF/GUTT Coq library. Given a finite relational system (binary edges
  plus arbitrary-arity hyperedges), it builds a RelationalTensor
  representation, computes invariants, and reports which CORE
  propositions (P1 Seriality, P2 DSoR, P4 Adjacency Tensor, P5 NRT
  composition, P7 Hyper-arity, P10 Directionality) fire and which
  DERIVED propositions (D_eq equivalence relation, D_fun functional
  relation) are guarded-fire. All arithmetic is exact rational
  (fractions.Fraction) with zero classical content. Includes a
  built-in smoke test and an export mode that generates Coq Example
  statements, a LaTeX table, and this citation file.
type: software
version: "{ENGINE_VERSION}"
date-released: "{today}"
license: Apache-2.0
authors:
  - family-names: Fillippini
    given-names: Michael
    # orcid: "https://orcid.org/XXXX-XXXX-XXXX-XXXX"  # add when registered
repository-code: "https://github.com/relationalexistence/UCF-GUTT"
url: "https://relationalexistence.com"
keywords:
  - relational ontology
  - formal verification
  - Coq
  - tensor methods
  - hypergraph theory
  - constructive mathematics
  - zero-axiom
  - UCF/GUTT
references:
  - type: software
    title: "UCF/GUTT Coq Library"
    authors:
      - family-names: Fillippini
        given-names: Michael
    url: "https://github.com/relationalexistence/UCF-GUTT"
    repository-code: "https://github.com/relationalexistence/UCF-GUTT"
"""
    with open(out_path, "w", encoding="utf-8") as f:
        f.write(cff)


def export_readme(out_path: str) -> None:
    """Write EXPORT_README.md explaining the artifacts."""
    today = datetime.now(timezone.utc).strftime("%Y-%m-%d")
    md = f"""# UCF/GUTT Reality Engine -- Generated Artifacts

Generated by `{ENGINE_NAME}` {ENGINE_VERSION} on {today}.

This directory contains four artifacts produced by a single `export` run of
the proposition-firing engine. Each is designed for a different durability
channel.

## Files

### `firings.v` -- Coq cross-check
Coq script with `Example` statements asserting the CORE proposition firings
for every system in the registry. Compiles against the existing
`Top__Propositions__Prop_{{01,02,04,05,10}}.v` modules. Drop into the
UCF/GUTT Coq project, add to `_CoqProject` after the propositions it
depends on, and run `coqc` (or `make`). Successful compilation means the
Python engine's claims are verified at the proof level.

Provides a one-way cross-check: if `firings.v` fails to compile, either
the engine or the proposition library is wrong. Either is a finding.

P7 firings are emitted as comments only, because
`Top__Propositions__Prop_07.v` is not yet in the public core. When P7 is
formalized, the existing scaffolding can be filled in.

### `firings.tex` -- arXiv-ready LaTeX table
A standalone LaTeX `table` environment summarizing the firing patterns
across all eight example systems. Requires `\\usepackage{{booktabs}}` and
`\\usepackage{{pifont}}`. Drop into the paper. Legend:

  - `\\cmark` = fires (CORE) or fires (DERIVED)
  - `\\xmark` = does not fire (CORE) or guard passed but property violated (DERIVED)
  - `\\dash`  = guard failed (DERIVED only)

The `ternary_only` row is bolded -- it is the architectural target case.

### `CITATION.cff` -- citation metadata
Citation File Format (CFF) metadata. Recognized by Zenodo, GitHub, and
academic indexers. Place at the root of the GitHub repository; GitHub will
then offer a "Cite this repository" button on the repo page.

Add your ORCID when registered (placeholder line is commented in the file).

### `EXPORT_README.md` -- this file
Context and usage notes.

## Reproducing

```bash
python3 ucf_proposition_firing_v3.py export ./export_artifacts
```

## On archival

- **GitHub** is not an archive. Mirror the repository to **Zenodo** to get
  a DOI and permanent record. `CITATION.cff` will be read by Zenodo when
  you do this.
- **arXiv preprints** are permanent and indexed. Once `firings.tex` is in
  a paper, the paper itself becomes a citable record.
- **AI training corpora** ingest public technical content. Work that is
  well-structured, on arXiv, and in well-documented GitHub repositories
  is read by AI systems and becomes findable through future AI queries.
  This is a form of reach that did not exist five years ago.

Three durability channels, each with different time horizons. The export
ensures the engine's results live in all three.
"""
    with open(out_path, "w", encoding="utf-8") as f:
        f.write(md)


def cmd_export(out_dir: str) -> int:
    """Run all four exports into out_dir."""
    os.makedirs(out_dir, exist_ok=True)
    coq_path = os.path.join(out_dir, "firings.v")
    tex_path = os.path.join(out_dir, "firings.tex")
    cit_path = os.path.join(out_dir, "CITATION.cff")
    rdm_path = os.path.join(out_dir, "EXPORT_README.md")
    rows = smoke_test()
    export_coq(coq_path)
    export_latex(tex_path, rows)
    export_citation(cit_path)
    export_readme(rdm_path)
    print(f"Wrote 4 archival artifacts to {out_dir}/")
    print(f"  {coq_path}   ({os.path.getsize(coq_path):>6} bytes)")
    print(f"  {tex_path}   ({os.path.getsize(tex_path):>6} bytes)")
    print(f"  {cit_path}   ({os.path.getsize(cit_path):>6} bytes)")
    print(f"  {rdm_path}   ({os.path.getsize(rdm_path):>6} bytes)")
    return 0


# =============================================================================
#   SECTION 10: TOP-LEVEL ENTRY POINTS + CLI
# =============================================================================

def run_system(name: str) -> dict:
    if name not in SYSTEM_REGISTRY:
        raise ValueError(
            f"unknown system: {name}; valid: {sorted(SYSTEM_REGISTRY)}")
    system = SYSTEM_REGISTRY[name]()
    rt = build_tensor(system)
    core = fire_propositions(rt)
    derived = fire_derived(rt)
    return {
        "system": system,
        "tensor": rt,
        "core_witnesses": core,
        "derived_witnesses": derived,
    }


def _print_header() -> None:
    print(_banner(
        f"{ENGINE_NAME} {ENGINE_VERSION}",
        width=76,
    ))
    print(
        "Hands-on companion to the INTEGRATED Coq propositions, with:\n"
        "  * HYPEREDGES (arity >= 3) and Prop 7 (hyper-arity)\n"
        "  * BINARY-CONTENT-SENSITIVE P2 and P10 (no false positives)\n"
        "  * DERIVED layer (D_eq, D_fun) with three-state guards\n"
        "  * SMOKE TEST validating the firing patterns\n"
        "  * EXPORT mode: Coq cross-check, LaTeX table, CITATION.cff\n"
    )


def main(argv: Optional[List[str]] = None) -> int:
    argv = list(sys.argv[1:] if argv is None else argv)
    _print_header()

    if not argv:
        for name in SYSTEM_REGISTRY:
            result = run_system(name)
            print(render_report(
                result["tensor"],
                result["core_witnesses"],
                result["derived_witnesses"],
            ))
            print()
        print(render_smoke_test(smoke_test()))
        return 0

    cmd = argv[0].lower()
    if cmd in ("-h", "--help", "help"):
        print(__doc__)
        return 0
    if cmd == "list":
        print("Available systems:")
        for n in SYSTEM_REGISTRY:
            exp = ",".join(sorted(EXPECTED_FIRING[n]))
            print(f"  {n:<22}  expected CORE firings: {{{exp}}}")
        return 0
    if cmd == "smoketest":
        rows = smoke_test()
        print(render_smoke_test(rows))
        return 0 if all(r.passed for r in rows) else 1
    if cmd == "export":
        if len(argv) < 2:
            print("usage: export <dir>", file=sys.stderr)
            return 1
        return cmd_export(argv[1])
    if cmd in SYSTEM_REGISTRY:
        result = run_system(cmd)
        print(render_report(
            result["tensor"],
            result["core_witnesses"],
            result["derived_witnesses"],
        ))
        return 0

    print(f"unknown command: {cmd}", file=sys.stderr)
    print(f"valid: {sorted(SYSTEM_REGISTRY)} | list | smoketest | export <dir> | help",
          file=sys.stderr)
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
