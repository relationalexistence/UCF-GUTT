"""
UCF/GUTT™ Core Relational Mathematics — DEMO VERSION
=====================================================

PROPRIETARY AND CONFIDENTIAL
Copyright (C) 2023-2026 Michael Fillippini. All Rights Reserved.

═══════════════════════════════════════════════════════════════════════════════
⚠️  INTELLECTUAL PROPERTY NOTICE
═══════════════════════════════════════════════════════════════════════════════

This file contains a SIMPLIFIED DEMONSTRATION implementation only.

WHAT THIS FILE IS:
  • A Python implementation that FOLLOWS the Coq specifications
  • Functionally similar behavior for DEMO PURPOSES
  • NOT the verified algorithms from the UCF/GUTT Coq library

WHAT THIS FILE IS NOT:
  • NOT formally verified code
  • NOT extracted from Coq proofs  
  • NOT the proprietary algorithms
  • NOT suitable for commercial use
  • NOT suitable for any application requiring mathematical guarantees

THE REAL VALUE IS IN:
  • 18,153 lines of Coq proofs (NOT INCLUDED)
  • Verified OCaml extraction (NOT INCLUDED)
  • Nested Relational Tensor algorithms (NOT INCLUDED)
  • Dimensional Sphere of Relation (NOT INCLUDED)
  • Temporal/Clock hierarchy structures (NOT INCLUDED)
  • Composition and transitivity rules (NOT INCLUDED)
  • WholeCompletion construction (NOT INCLUDED)

REVERSE ENGINEERING NOTICE:
  The "algorithms" visible here (e.g., has_positive AND has_negative) are
  TRIVIALLY OBVIOUS and constitute no trade secret. Any competent programmer
  could write the same logic in minutes. The intellectual property value lies
  in the FORMAL PROOFS that guarantee these simple checks are mathematically
  correct within a complete relational ontology — none of which is included.

LICENSING:
  For access to verified implementations, Coq source code, and commercial
  rights, contact: relationalexistence.com

═══════════════════════════════════════════════════════════════════════════════

VERIFICATION STATUS:
- If libucf_gutt.so is present: Uses VERIFIED code extracted from Coq
- Otherwise: Uses Python implementation following Coq specifications

FORMAL BACKING (in Coq library — NOT INCLUDED):
- WeightedRel: Top__Relations__Weighted.v
- Seriality: Top__Propositions__Prop_01.v  
- MultiplexRel: Top__Relations__Weighted.v (Section 4)
- Conflict/Harmony: WR.R_conflict, WR.R_harmony
"""

# ═══════════════════════════════════════════════════════════════════════════════
# DEMO IMPLEMENTATION BELOW — NOT PROPRIETARY
# The logic here is intentionally simple and obvious.
# The value is in the PROOFS, not in these trivial predicates.
# ═══════════════════════════════════════════════════════════════════════════════

# Try to import verified bridge
try:
    from ucf_verified_bridge import (
        check_conflict as _verified_conflict,
        check_harmony as _verified_harmony,
        check_support as _verified_support,
        is_verified_available,
        get_verification_status
    )
    _HAS_VERIFIED_BRIDGE = True
except ImportError:
    _HAS_VERIFIED_BRIDGE = False
    def is_verified_available():
        return False
    def get_verification_status():
        return "DEMO MODE: Python implementation (verified mode requires license)"

from dataclasses import dataclass, field
from typing import Dict, List, Set, Tuple, Optional, TypeVar, Generic, Callable
from enum import Enum
from fractions import Fraction
import json

# Type variable for universe elements
T = TypeVar('T')


class RelationSign(Enum):
    """
    Relational polarity.
    
    Formal basis: WR.wr_sign in Top__Relations__Weighted.v
    
    NOTE: This enum definition is NOT proprietary. The proprietary content
    is the formal proof that this classification is exhaustive and that
    the sign algebra satisfies required properties.
    """
    POSITIVE = 1    # Cooperative/harmonic relation
    ZERO = 0        # No relation
    NEGATIVE = -1   # Antagonistic/conflict relation


@dataclass
class WeightedEdge:
    """
    A single weighted directed edge.
    
    Formal basis: WeightedRel U := U -> U -> Q
    in Top__Relations__Weighted.v lines 96-98
    """
    source: str
    target: str
    weight: Fraction
    
    @property
    def sign(self) -> RelationSign:
        """
        Extract sign of relation.
        
        Formal basis: WR.wr_sign (lines 280-295)
        Theorem: sign_magnitude_decomposition proves W = sign * |W|
        """
        if self.weight > 0:
            return RelationSign.POSITIVE
        elif self.weight < 0:
            return RelationSign.NEGATIVE
        else:
            return RelationSign.ZERO
    
    @property
    def magnitude(self) -> Fraction:
        """
        Absolute value of weight.
        
        Formal basis: WR.wr_abs (lines 111-112)
        """
        return abs(self.weight)
    
    @property
    def has_support(self) -> bool:
        """
        Does this relation exist (non-zero)?
        
        Formal basis: R_support (lines 141-142)
        Definition: R_support W a b := ~ W a b == 0
        """
        return self.weight != 0


class WeightedRelation(Generic[T]):
    """
    A weighted relation on a universe of entities.
    
    Formal basis: Definition WeightedRel (U : Type) := U -> U -> Q.
    (Top__Relations__Weighted.v line 98)
    
    Key properties proven in Coq:
    - pos_implies_support: 0 < W a b -> R_support W a b
    - neg_implies_support: W a b < 0 -> R_support W a b  
    - support_iff_pos_or_neg: R_support <-> (R_pos or R_neg)
    """
    
    def __init__(self, entities: List[str]):
        self.entities: Set[str] = set(entities)
        self._weights: Dict[Tuple[str, str], Fraction] = {}
    
    def set_weight(self, source: str, target: str, weight: Fraction) -> None:
        """Set the weight of relation from source to target."""
        if source not in self.entities:
            self.entities.add(source)
        if target not in self.entities:
            self.entities.add(target)
        self._weights[(source, target)] = weight
    
    def get_weight(self, source: str, target: str) -> Fraction:
        """
        Get weight, defaulting to 0 (no relation).
        
        Formal basis: This matches Coq's function semantics where
        undefined pairs return 0.
        """
        return self._weights.get((source, target), Fraction(0))
    
    def get_edge(self, source: str, target: str) -> WeightedEdge:
        """Get edge as WeightedEdge object."""
        return WeightedEdge(source, target, self.get_weight(source, target))
    
    def has_support(self, source: str, target: str) -> bool:
        """
        Check if relation exists.
        
        Formal basis: R_support in Top__Relations__Weighted.v
        """
        return self.get_weight(source, target) != 0
    
    def is_positive(self, source: str, target: str) -> bool:
        """
        Check if relation is cooperative.
        
        Formal basis: R_pos W a b := 0 < W a b (line 145-146)
        """
        return self.get_weight(source, target) > 0
    
    def is_negative(self, source: str, target: str) -> bool:
        """
        Check if relation is antagonistic.
        
        Formal basis: R_neg W a b := W a b < 0 (line 149-150)
        """
        return self.get_weight(source, target) < 0
    
    def all_edges(self) -> List[WeightedEdge]:
        """Return all non-zero edges."""
        return [
            WeightedEdge(s, t, w) 
            for (s, t), w in self._weights.items() 
            if w != 0
        ]
    
    def outgoing(self, entity: str) -> List[WeightedEdge]:
        """All outgoing edges from an entity."""
        return [
            WeightedEdge(entity, t, w)
            for (s, t), w in self._weights.items()
            if s == entity and w != 0
        ]
    
    def incoming(self, entity: str) -> List[WeightedEdge]:
        """All incoming edges to an entity."""
        return [
            WeightedEdge(s, entity, w)
            for (s, t), w in self._weights.items()
            if t == entity and w != 0
        ]


class MultiplexRelation:
    """
    Multiple simultaneous relationship channels between entities.
    
    Formal basis: Definition MultiplexRel (K U : Type) := K -> WeightedRel U.
    (Top__Relations__Weighted.v line 407)
    
    Key theorems from Coq:
    - R_conflict: exists positive AND negative channels
    - R_harmony: all channels have same sign (or zero)
    """
    
    def __init__(self, entities: List[str], channels: List[str]):
        self.entities = set(entities)
        self.channels = channels
        self._relations: Dict[str, WeightedRelation] = {
            ch: WeightedRelation(entities) for ch in channels
        }
    
    def set_weight(self, channel: str, source: str, target: str, weight: Fraction) -> None:
        """Set weight on a specific channel."""
        if channel not in self._relations:
            self._relations[channel] = WeightedRelation(list(self.entities))
            self.channels.append(channel)
        self._relations[channel].set_weight(source, target, weight)
        self.entities.add(source)
        self.entities.add(target)
    
    def get_weight(self, channel: str, source: str, target: str) -> Fraction:
        """Get weight on a specific channel."""
        if channel not in self._relations:
            return Fraction(0)
        return self._relations[channel].get_weight(source, target)
    
    def get_channel(self, channel: str) -> Optional[WeightedRelation]:
        """Get entire channel relation."""
        return self._relations.get(channel)
    
    def has_conflict(self, source: str, target: str) -> bool:
        """
        Detect if relationship has conflicting signals across channels.
        
        Formal basis: R_conflict in Top__Relations__Weighted.v (lines 444-446)
        Definition R_conflict M channels a b :=
          (exists k1, In k1 channels /\\ R_pos (M k1) a b) /\\
          (exists k2, In k2 channels /\\ R_neg (M k2) a b).
          
        VERIFICATION: When verified library is loaded, this calls the
        OCaml function extracted directly from the Coq proof.
        """
        # Collect weights for this pair
        weights = {ch: self.get_weight(ch, source, target) for ch in self.channels}
        
        # Use verified implementation if available
        if _HAS_VERIFIED_BRIDGE and is_verified_available():
            return _verified_conflict(weights)
        
        # Otherwise use Python implementation following spec
        has_positive = False
        has_negative = False
        
        for w in weights.values():
            if w > 0:
                has_positive = True
            elif w < 0:
                has_negative = True
        
        return has_positive and has_negative
    
    def has_harmony(self, source: str, target: str) -> bool:
        """
        Check if all channels are aligned (same sign or zero).
        
        Formal basis: R_harmony in Top__Relations__Weighted.v (lines 449-453)
        
        Harmony means no conflict - either all positive, all negative,
        or mixture of same-sign and zeros.
        
        VERIFICATION: When verified library is loaded, this uses the
        PROVEN implementation extracted from Coq.
        """
        # Collect weights for this pair
        weights = {ch: self.get_weight(ch, source, target) for ch in self.channels}
        
        # Use verified implementation if available
        if _HAS_VERIFIED_BRIDGE and is_verified_available():
            return _verified_harmony(weights)
        
        # Otherwise use Python implementation following spec
        signs_seen = set()
        
        for w in weights.values():
            if w > 0:
                signs_seen.add(RelationSign.POSITIVE)
            elif w < 0:
                signs_seen.add(RelationSign.NEGATIVE)
            # Zero doesn't count
        
        # Harmony: at most one non-zero sign type
        return len(signs_seen) <= 1
    
    def aggregate_weight(self, source: str, target: str) -> Fraction:
        """
        Sum weights across all channels.
        
        Formal basis: mpx_sum in Top__Relations__Weighted.v (lines 415-416)
        """
        return sum(
            self.get_weight(ch, source, target) 
            for ch in self.channels
        )
    
    def conflict_pairs(self) -> List[Tuple[str, str]]:
        """Find all entity pairs with conflicting channel signals."""
        conflicts = []
        for s in self.entities:
            for t in self.entities:
                if s != t and self.has_conflict(s, t):
                    conflicts.append((s, t))
        return conflicts
    
    def harmony_pairs(self) -> List[Tuple[str, str]]:
        """Find all entity pairs with harmonious channel signals."""
        harmonious = []
        for s in self.entities:
            for t in self.entities:
                if s != t and self.has_harmony(s, t):
                    # Only include if there's at least one non-zero channel
                    if any(self.get_weight(ch, s, t) != 0 for ch in self.channels):
                        harmonious.append((s, t))
        return harmonious


def check_seriality(relation: WeightedRelation, whole_entity: str = "__WHOLE__") -> Tuple[bool, List[str]]:
    """
    Check if relation satisfies seriality (every entity has outgoing edge).
    
    Formal basis: Proposition 01 in Top__Propositions__Prop_01.v
    
    THEOREM (proposition_01):
      forall (U : Type) (R : U -> U -> Prop) (x : Ux U),
        exists y : Ux U, R_prime R x y.
        
    "Every entity in the extended universe has at least one outgoing edge"
    
    In UCF/GUTT, seriality is GUARANTEED by adding the "Whole" - a universal
    sink that everything relates to. This function checks seriality and
    identifies violations (entities with no outgoing edges).
    
    Returns: (is_serial, list of violating entities)
    """
    violations = []
    
    for entity in relation.entities:
        if entity == whole_entity:
            continue
        
        has_outgoing = any(
            relation.has_support(entity, other)
            for other in relation.entities
            if other != entity
        )
        
        if not has_outgoing:
            violations.append(entity)
    
    return (len(violations) == 0, violations)


def ensure_seriality(relation: WeightedRelation, whole_entity: str = "__WHOLE__") -> WeightedRelation:
    """
    Ensure seriality by adding Whole completion.
    
    Formal basis: WholeCompletion in Top__Extensions__WholeCompletion.v
    
    This is the CONSTRUCTIVE proof from Proposition 01:
    - Add a distinguished "Whole" entity
    - Every entity relates to Whole with weight 1
    - This GUARANTEES seriality by construction
    
    THEOREM (from Coq): After WholeCompletion, Serial (lift R) holds.
    """
    # Add Whole to entities
    relation.entities.add(whole_entity)
    
    # Every entity relates to Whole
    for entity in relation.entities:
        if entity != whole_entity:
            # Set relation to Whole if not already set
            if not relation.has_support(entity, whole_entity):
                relation.set_weight(entity, whole_entity, Fraction(1))
    
    # Whole relates to itself (point_self_loop from Coq)
    relation.set_weight(whole_entity, whole_entity, Fraction(1))
    
    return relation


# Aggregate metrics following verified specifications

def relation_density(relation: WeightedRelation) -> Fraction:
    """
    Proportion of possible edges that exist.
    
    This is a standard metric, but computed over the formally-specified
    support predicate (non-zero weight).
    """
    n = len(relation.entities)
    if n <= 1:
        return Fraction(0)
    
    possible = n * (n - 1)  # Directed, no self-loops counted
    actual = sum(1 for e in relation.all_edges() if e.source != e.target)
    
    return Fraction(actual, possible)


def sentiment_balance(relation: WeightedRelation) -> Fraction:
    """
    Ratio of positive to total weighted magnitude.
    
    Returns value in [-1, 1]:
    - 1 means all positive
    - -1 means all negative  
    - 0 means balanced or no relations
    """
    total_positive = sum(e.weight for e in relation.all_edges() if e.weight > 0)
    total_negative = sum(abs(e.weight) for e in relation.all_edges() if e.weight < 0)
    
    total = total_positive + total_negative
    if total == 0:
        return Fraction(0)
    
    return (total_positive - total_negative) / total


def multiplex_alignment_score(mpx: MultiplexRelation) -> Fraction:
    """
    Proportion of relationships that are harmonious (vs conflicting).
    
    Based on R_harmony / R_conflict predicates from Coq.
    """
    harmony_count = 0
    conflict_count = 0
    total_with_relations = 0
    
    for s in mpx.entities:
        for t in mpx.entities:
            if s == t:
                continue
            
            # Check if any channel has a relation
            has_any = any(mpx.get_weight(ch, s, t) != 0 for ch in mpx.channels)
            if not has_any:
                continue
                
            total_with_relations += 1
            
            if mpx.has_conflict(s, t):
                conflict_count += 1
            elif mpx.has_harmony(s, t):
                harmony_count += 1
    
    if total_with_relations == 0:
        return Fraction(1)  # Vacuously harmonious
    
    return Fraction(harmony_count, total_with_relations)
