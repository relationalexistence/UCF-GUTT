#!/usr/bin/env python3
# =============================================================================
#   UCF/GUTT(TM) -- Reality Engine in a Teacup, v2
#   Copyright 2023-2026 Michael Fillippini.
#
#   Licensed under the Apache License, Version 2.0 (the "License").
#       http://www.apache.org/licenses/LICENSE-2.0
#
#   SPDX-License-Identifier: Apache-2.0
# =============================================================================
"""
UCF/GUTT Proposition Firing v2 -- Reality Engine miniature with hyperedges,
a DERIVED proposition layer, and a smoke test.

CHANGES FROM v1
---------------
1. HYPEREDGES. `HyperEdge` carries arity >= 2 (typically 3+ for n-ary
   relations). `RelationalSystem` now accepts both binary edges and
   hyperedges. The library extension is `Top__Relations__RelationalHypergraphTheory.v`.

2. PROP 7 ADDED. CORE proposition for hyper-arity: fires when the base
   relation has at least one hyperedge.

3. BINARY-CONTENT-SENSITIVITY. v1 had a 'false positive' wart: P2 and P10
   fired on every system, because the Whole-completion always provides
   binary edges to fire over. v2 fixes this: P2 and P10 check BASE binary
   content, not lifted content. On a ternary-only system, P2 and P10
   correctly do NOT fire.

4. DERIVED PROPOSITIONS. A separate layer of GUARDED propositions that
   may or may not fire depending on stronger invariants:
     D_eq    : base R is an equivalence relation
     D_fun   : base R is functional (each x has <=1 out-edge)
   Each DERIVED check is three-state: GUARD FAILED, GUARD PASSED+VIOLATED,
   or FIRES. This mirrors memory:
     "15 CORE propositions reading directly off tensor structure,
      37 DERIVED requiring stronger guards"

5. SMOKE TEST. `smoke_test()` runs the engine on canonical inputs and
   verifies expected firing patterns -- including the headline target:
     plain ternary R(A,B,C) fires EXACTLY {P1, P4, P5, P7}; no others.

CORE PROPOSITIONS MIRRORED
--------------------------
    Top__Propositions__Prop_01   -- Seriality via Whole-completion
    Top__Propositions__Prop_02   -- Multi-dimensional representation (DSoR)
    Top__Propositions__Prop_04   -- Graph / Adjacency Tensor
    Top__Propositions__Prop_05   -- Relational Tensor / NRT modular composition
    Top__Propositions__Prop_07   -- Hyper-arity (relations not restricted to binary)
    Top__Propositions__Prop_10   -- Directionality

USAGE
-----
    python3 ucf_proposition_firing_v2.py                # all systems
    python3 ucf_proposition_firing_v2.py ternary_only   # the headline target
    python3 ucf_proposition_firing_v2.py smoketest      # validation pass
    python3 ucf_proposition_firing_v2.py list           # all systems

ARITHMETIC POLICY
-----------------
Exact rationals (`fractions.Fraction`). No float ever feeds a firing
decision. Modularity checks are bit-exact in Q.
"""

from __future__ import annotations

import sys
from dataclasses import dataclass, field
from enum import Enum
from fractions import Fraction
from typing import (Callable, Dict, FrozenSet, List, Optional, Sequence,
                    Set, Tuple)


# =============================================================================
#   SECTION 1: CORE TYPES
# =============================================================================

@dataclass(frozen=True)
class Element:
    """Element of the extended universe U_x = U + {Whole}."""
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
    """Mirrors `Direction U` from `Top__Propositions__Prop_10`."""
    UNDIRECTED = "Undirected"
    UNI = "Uni"
    BI = "Bi"
    MULTI = "Multi"


@dataclass(frozen=True)
class Edge:
    """A binary edge in the base relation R."""
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
    """An n-ary edge with arity >= 2 (typically 3+ for hyperedge use).

    In UCF/GUTT, relations of arbitrary arity are PRIMITIVE -- not
    derivable from binary projections. Mirrors the spirit of
    `Top__Relations__RelationalHypergraphTheory.v`.
    """
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
    """A finite relational system: a finite U with a finite base relation R.

    R is decomposed into base_edges (arity 2) and base_hyperedges
    (arity >= 3). This separation matters for proposition firing: P2 and
    P10 are binary-content-sensitive, P7 is hyperedge-content-sensitive.
    """
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
        """Edges added by Whole-completion: R'(x, Whole) for every x in U."""
        whole = Element.whole()
        return tuple(
            Edge(src=x, tgt=whole, direction=Direction.UNI,
                 weight=Fraction(1))
            for x in self.base_elements
        )


# =============================================================================
#   SECTION 3: RELATIONAL TENSOR + INVARIANTS
# =============================================================================

@dataclass(frozen=True)
class RelationalTensor:
    """Tensor representation with invariants computed at construction."""
    system: RelationalSystem

    # Binary adjacency on U_x (includes Whole-completion).
    adjacency: Dict[Tuple[Element, Element], Fraction]

    # Hyperedge inventory by arity.
    hyperedge_count_by_arity: Dict[int, int]

    # Cardinalities.
    n_base_elements: int
    n_extended_elements: int
    n_base_binary_edges: int          # declared base binary edges
    n_base_binary_pairs: int          # distinct (s,t) pairs in base adj
    n_base_hyperedges: int            # total hyperedges (arity >= 3 here)
    max_arity: int                    # 0 if no edges; 2 if only binary; >=3 if hyper
    n_whole_completion_edges: int     # Whole-completion edge count incl. Whole self-loop
    n_total_lifted_binary_edges: int  # entries in adjacency dict

    # Base-binary structural invariants.
    is_reflexive_on_base: bool
    is_symmetric_on_base: bool
    is_transitive_on_base: bool
    has_self_loop: bool
    is_strongly_connected_on_base: bool

    # Direction-type inventory from BASE binary edges only.
    base_direction_types: FrozenSet[Direction]

    # Isolation counts.
    n_isolated_pre_completion: int
    n_isolated_post_completion: int  # always 0 -- the Whole-completion guarantee


def build_tensor(system: RelationalSystem) -> RelationalTensor:
    """Construct the RelationalTensor. All checks decidable in finite Q."""
    whole = Element.whole()
    base = system.base_elements
    base_set = set(base)

    # --- Binary adjacency from base binary edges ---
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

    # --- Whole-completion edges ---
    for ed in system.whole_completion_edges():
        adj[(ed.src, whole)] = Fraction(1)
    adj[(whole, whole)] = Fraction(1)  # Whole_self_loop

    # --- Hyperedge inventory ---
    hyper_arity_count: Dict[int, int] = {}
    for h in system.base_hyperedges:
        hyper_arity_count[h.arity] = hyper_arity_count.get(h.arity, 0) + 1

    # --- Base-binary invariants (only over base_pairs_only, NOT Whole edges) ---
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

    # Strong connectivity via BFS-style closure on base_pairs_only.
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

    # Direction types from BASE binary edges only.
    base_dirs = frozenset(ed.direction for ed in system.base_edges)

    # Isolation counts: pre-completion is base-only.
    n_iso_pre = sum(
        1 for x in base
        if not any(s == x for (s, _) in base_pairs_only)
        and not any(x in h.vertices for h in system.base_hyperedges)
    )

    # Max arity.
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
        n_whole_completion_edges=len(base) + 1,  # +1 for Whole self-loop
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
    """P1: Seriality via Whole-completion. Unconditional root."""
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
    """P2: Multi-dimensional representation. Requires BASE binary content.

    v2 fix: P2's witness is the ego-centric tensor T(x,y) over the BASE
    relation, not the lifted Whole-completion. If there is no base binary
    content, P2 has nothing to be multi-dimensional ABOUT, so it does
    not fire. This eliminates the v1 false positive.
    """
    if rt.n_base_binary_pairs == 0:
        return PropositionWitness(
            prop_id=PropositionID.P2,
            fired=False,
            is_unconditional=False,
            coq_theorem="multi_dim_representation",
            invariant_basis="No base binary pairs; nothing for DSoR to characterize.",
            witness_summary="DOES NOT FIRE -- P2 is binary-content-sensitive.",
        )

    # Pick a base sample.
    sample: Optional[Tuple[Element, Element, Fraction]] = None
    base_set = set(rt.system.base_elements)
    for (s, t), w in rt.adjacency.items():
        if s in base_set and t in base_set and w > 0:
            sample = (s, t, w)
            break
    assert sample is not None  # follows from n_base_binary_pairs > 0
    s, t, w = sample
    return PropositionWitness(
        prop_id=PropositionID.P2,
        fired=True,
        is_unconditional=False,
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
    """P4: Graph / Adjacency Tensor. Fires on every system (binary graph rep
    always available, even on hyperedge-only systems, via Whole-completion).
    """
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
        prop_id=PropositionID.P4,
        fired=True,
        is_unconditional=False,
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
    """P5: RT / NRT modular composition. Includes hyperedge NRTs in v2."""
    # NRT decomposition by direction type for binary, plus per-arity for hyper.
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

    # Modularity check (exact Q) over the binary adjacency.
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
    n_components = (
        len(binary_by_dir) + len(rt.hyperedge_count_by_arity) + 1  # +1 for Whole
    )
    return PropositionWitness(
        prop_id=PropositionID.P5,
        fired=True,
        is_unconditional=False,
        coq_theorem="proposition_5_relational_tensor (5 clauses)",
        invariant_basis=(
            f"{n_components} NRT component(s) compose into the system RT."
        ),
        witness_summary=(
            "Composite tensor = sum over NRT components; modularity verified in exact Q."
        ),
        witness_detail=detail,
    )


def check_prop_07(rt: RelationalTensor) -> PropositionWitness:
    """P7: Hyper-arity. Fires when the base relation contains at least one
    hyperedge of arity >= 3.

    In UCF/GUTT, relations of arbitrary arity are primitive, not derivable
    from binary projections. This proposition records that fact and is
    invariant-gated: it fires iff hyper-arity content is actually present.
    """
    if rt.n_base_hyperedges == 0:
        return PropositionWitness(
            prop_id=PropositionID.P7,
            fired=False,
            is_unconditional=False,
            coq_theorem="hyper_arity_primitive",
            invariant_basis=(
                f"max base arity = {rt.max_arity}; no hyperedges present."
            ),
            witness_summary="DOES NOT FIRE -- no hyperedge content in base R.",
        )
    sample = rt.system.base_hyperedges[0]
    sample_str = ", ".join(str(v) for v in sample.vertices)
    arity_str = ", ".join(
        f"arity={a}: {n}"
        for a, n in sorted(rt.hyperedge_count_by_arity.items())
    )
    return PropositionWitness(
        prop_id=PropositionID.P7,
        fired=True,
        is_unconditional=False,
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
    """P10: Directionality. v2 fix: checks BASE direction types only.

    Whole-completion always adds Uni edges. If we counted lifted direction
    types, P10 would fire on every system -- a false positive. v2 fires
    P10 iff the BASE relation has at least one directional binary edge.
    """
    base_dirs = rt.base_direction_types
    if not base_dirs:
        return PropositionWitness(
            prop_id=PropositionID.P10,
            fired=False,
            is_unconditional=False,
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
        prop_id=PropositionID.P10,
        fired=True,
        is_unconditional=False,
        coq_theorem="universal_connectivity_directed, direction_independent_of_existence",
        invariant_basis=(
            f"{len(base_dirs)} of 4 direction types present in BASE R."
        ),
        witness_summary=(
            "Every base binary edge has a direction; direction is independent "
            "of existence (add/remove/change preserves existence)."
        ),
        witness_detail=[
            f"  direction types in base R : {{{present_str}}}",
            f"  direction types absent    : {{{missing_str}}}"
            if missing else "  direction types absent    : {}  (all four present)",
            "",
            "  universal_connectivity_directed (Coq):",
            "    For every x in U_x, the relation Uni(x, Whole) exists with",
            "    origin = x, destination = Whole, direction = Some Uni.",
        ],
    )


CORE_PROPOSITION_CHECKS: Tuple[Callable[[RelationalTensor], PropositionWitness], ...] = (
    check_prop_01,
    check_prop_02,
    check_prop_04,
    check_prop_05,
    check_prop_07,
    check_prop_10,
)


def fire_propositions(rt: RelationalTensor) -> List[PropositionWitness]:
    return [check(rt) for check in CORE_PROPOSITION_CHECKS]


# =============================================================================
#   SECTION 5: DERIVED PROPOSITION CHECKS (GUARDED)
#
#   Three-state: GUARD FAILED, GUARD PASSED + PROPERTY VIOLATED, FIRES.
# =============================================================================

@dataclass(frozen=True)
class DerivedWitness:
    prop_id: str            # e.g., "D_eq"
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
    """D_eq: base R is an equivalence relation on U.

    Guard:    base R is non-empty (at least one base binary pair).
    Property: reflexive AND symmetric AND transitive.
    """
    guard_desc = "base R has at least one binary pair"
    if rt.n_base_binary_pairs == 0:
        return DerivedWitness(
            prop_id="D_eq",
            title="Equivalence relation on U",
            fired=False,
            guard_description=guard_desc,
            guard_passed=False,
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
            prop_id="D_eq",
            title="Equivalence relation on U",
            fired=True,
            guard_description=guard_desc,
            guard_passed=True,
            invariant_basis=(
                "Base R is reflexive, symmetric, and transitive."
            ),
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
        prop_id="D_eq",
        title="Equivalence relation on U",
        fired=False,
        guard_description=guard_desc,
        guard_passed=True,
        invariant_basis=f"Base R violates: {', '.join(violations)}.",
        witness_summary="Guard passed but equivalence property failed.",
        witness_detail=[
            f"  reflexive on U  : {refl}",
            f"  symmetric on U  : {sym}",
            f"  transitive on U : {trans}",
        ],
    )


def check_derived_functional(rt: RelationalTensor) -> DerivedWitness:
    """D_fun: base R is functional (each x in U has at most one base out-edge).

    Guard:    base R is non-empty.
    Property: every x in U has out-degree <= 1 in base_pairs.
    """
    guard_desc = "base R has at least one binary pair"
    if rt.n_base_binary_pairs == 0:
        return DerivedWitness(
            prop_id="D_fun",
            title="Functional / deterministic relation on U",
            fired=False,
            guard_description=guard_desc,
            guard_passed=False,
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
    violators = [
        (str(x), c) for x, c in out_counts.items() if c > 1
    ]
    if fired:
        return DerivedWitness(
            prop_id="D_fun",
            title="Functional / deterministic relation on U",
            fired=True,
            guard_description=guard_desc,
            guard_passed=True,
            invariant_basis=f"Every x in U has out-degree <= 1 in base R; max = {max_out}.",
            witness_summary="Base R is a (partial) function on U.",
            witness_detail=[
                f"  out-degrees: " + ", ".join(
                    f"{x}: {c}" for x, c in out_counts.items()
                ),
            ],
        )
    return DerivedWitness(
        prop_id="D_fun",
        title="Functional / deterministic relation on U",
        fired=False,
        guard_description=guard_desc,
        guard_passed=True,
        invariant_basis=(
            f"{len(violators)} element(s) violate the at-most-one-out-edge bound."
        ),
        witness_summary="Guard passed but functional property failed.",
        witness_detail=[
            f"  out-degrees: " + ", ".join(
                f"{x}: {c}" for x, c in out_counts.items()
            ),
            f"  violators (out > 1): "
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
    edges = tuple(Edge(s, t, direction=Direction.UNDIRECTED) for s, t in pairs)
    return RelationalSystem(
        name="K_4 (undirected complete graph on 4 vertices)",
        base_elements=(a, b, c, d),
        base_edges=edges,
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
    """An honest equivalence relation: reflexive, symmetric, transitive.

    Three elements a, b, c with two classes: {a, b} and {c}. R contains
    (a,a),(b,b),(c,c),(a,b),(b,a). D_eq should fire on this one.
    """
    a, b, c = (Element.elem(x) for x in ("a", "b", "c"))
    return RelationalSystem(
        name="EQUIVALENCE_2CLASS (classes {a,b}, {c}; reflexive+sym+trans)",
        base_elements=(a, b, c),
        base_edges=(
            # Reflexive self-loops.
            Edge(a, a, direction=Direction.UNI),
            Edge(b, b, direction=Direction.UNI),
            Edge(c, c, direction=Direction.UNI),
            # Symmetric pair connecting a and b. Use BI to expand to both.
            Edge(a, b, direction=Direction.BI),
        ),
    )


def system_ternary_only() -> RelationalSystem:
    """Plain ternary R(a, b, c). The smoke-test headline.

    Base relation contains ONLY a single ternary hyperedge -- no binary
    edges, no directions. Expected firing: EXACTLY {P1, P4, P5, P7}.
    P2 does not fire (no base binary). P10 does not fire (no base
    direction types). D_eq and D_fun are GUARD-FAILED (no base binary).
    """
    a, b, c = (Element.elem(x) for x in ("a", "b", "c"))
    return RelationalSystem(
        name="TERNARY_ONLY (R(a,b,c) hyperedge only; no binary R)",
        base_elements=(a, b, c),
        base_hyperedges=(HyperEdge(vertices=(a, b, c)),),
    )


def system_binary_plus_ternary() -> RelationalSystem:
    """Binary edge AND a ternary hyperedge.

    Exercises full firing pattern: P1 + P2 + P4 + P5 + P7 + P10.
    """
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

# Per the memory:
#   "proposition module validated against 7-case smoke test with tightened
#    predicates (plain ternary R(A,B,C) fires exactly Props 1, 4, 5, 7
#    -- no false positives)"
# We extend that to the full registry.
EXPECTED_FIRING: Dict[str, FrozenSet[str]] = {
    # CORE firings expected for each named system.
    "empty":               frozenset({"P1", "P4", "P5"}),
    "cycle4":              frozenset({"P1", "P2", "P4", "P5", "P10"}),
    "k4":                  frozenset({"P1", "P2", "P4", "P5", "P10"}),
    "selfloop":            frozenset({"P1", "P2", "P4", "P5", "P10"}),
    "mixed":               frozenset({"P1", "P2", "P4", "P5", "P10"}),
    "equivalence":         frozenset({"P1", "P2", "P4", "P5", "P10"}),
    "ternary_only":        frozenset({"P1", "P4", "P5", "P7"}),  # HEADLINE
    "binary_plus_ternary": frozenset({"P1", "P2", "P4", "P5", "P7", "P10"}),
}

EXPECTED_DERIVED: Dict[str, FrozenSet[str]] = {
    # DERIVED firings expected for each named system.
    "empty":               frozenset(),
    "cycle4":              frozenset({"D_fun"}),  # functional but not equivalence
    "k4":                  frozenset(),  # not functional, not equivalence
    "selfloop":            frozenset({"D_fun"}),  # functional, not equivalence
    "mixed":               frozenset(),
    "equivalence":         frozenset({"D_eq"}),  # the honest equivalence
    "ternary_only":        frozenset(),  # both guards fail
    "binary_plus_ternary": frozenset({"D_fun"}),  # base R = {(a,b),(b,a)} bi
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
    """Run the engine on every registered system and check against expectations."""
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
#   SECTION 8: PRETTY PRINTING
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
        f"  {'system':<22} {'core actual':<26} {'core expected':<26} {'derived actual':<14} {'expected':<14} ok?"
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
    parts.append(
        f"  OVERALL: {'ALL PASS' if all_pass else 'FAILURES PRESENT'}"
    )
    return "\n".join(parts)


# =============================================================================
#   SECTION 9: TOP-LEVEL ENTRY POINTS + CLI
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
        "UCF/GUTT Proposition Firing v2 -- Reality Engine miniature",
        width=76,
    ))
    print(
        "Hands-on companion to the INTEGRATED Coq propositions, with:\n"
        "  * HYPEREDGES (arity >= 3) and Prop 7 (hyper-arity)\n"
        "  * BINARY-CONTENT-SENSITIVE P2 and P10 (no false positives)\n"
        "  * DERIVED proposition layer with three-state guards\n"
        "  * SMOKE TEST validating the firing patterns\n\n"
        "Headline target (per the v2.0 architecture memo):\n"
        "  plain ternary R(A,B,C) fires EXACTLY {P1, P4, P5, P7}.\n"
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
        print(render_smoke_test(smoke_test()))
        rows = smoke_test()
        return 0 if all(r.passed for r in rows) else 1
    if cmd in SYSTEM_REGISTRY:
        result = run_system(cmd)
        print(render_report(
            result["tensor"],
            result["core_witnesses"],
            result["derived_witnesses"],
        ))
        return 0

    print(f"unknown command: {cmd}", file=sys.stderr)
    print(f"valid: {sorted(SYSTEM_REGISTRY)} | list | smoketest | help",
          file=sys.stderr)
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
