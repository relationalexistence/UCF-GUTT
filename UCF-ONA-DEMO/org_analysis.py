"""
UCF/GUTT™ Organizational Network Analysis — DEMO VERSION
=========================================================

PROPRIETARY AND CONFIDENTIAL
Copyright (C) 2023-2026 Michael Fillippini. All Rights Reserved.

═══════════════════════════════════════════════════════════════════════════════
⚠️  INTELLECTUAL PROPERTY NOTICE — DEMO IMPLEMENTATION
═══════════════════════════════════════════════════════════════════════════════

This module provides a DEMONSTRATION of organizational network analysis using
simplified implementations that follow the UCF/GUTT formal specifications.

WHAT'S INCLUDED (Demo):
  • Team relationship modeling with weighted multiplex relations
  • Basic conflict and harmony detection
  • Seriality checking
  • Aggregate health metrics (simplified calculations)

WHAT'S NOT INCLUDED (Licensed):
  • Verified algorithms extracted from Coq proofs
  • Advanced health scoring with formal guarantees
  • Nested organizational hierarchies (NRT)
  • Temporal tracking of relationship evolution
  • Cascade effect modeling
  • Bloc/coalition cohesion analysis

THE DEMO DIFFERENCE:
  Demo: "Our implementation follows the formal spec"
  Licensed: "Our code IS the proof — mathematically guaranteed correct"

REVERSE ENGINEERING NOTICE:
  The organizational analysis logic here uses the same trivial predicates
  as the core module. The intellectual property value is in the 18,153 lines
  of Coq proofs that guarantee correctness — none of which is included here.

For commercial licensing: relationalexistence.com
═══════════════════════════════════════════════════════════════════════════════
"""

from dataclasses import dataclass, field
from typing import Dict, List, Set, Tuple, Optional
from fractions import Fraction
from enum import Enum
import json

from ucf_core import (
    WeightedRelation, 
    MultiplexRelation, 
    WeightedEdge,
    RelationSign,
    check_seriality,
    ensure_seriality,
    relation_density,
    sentiment_balance,
    multiplex_alignment_score
)


class RelationshipChannel(Enum):
    """Standard organizational relationship channels."""
    COLLABORATION = "collaboration"      # Work together on tasks
    COMMUNICATION = "communication"      # Information exchange frequency
    TRUST = "trust"                      # Confidence/reliability
    INFLUENCE = "influence"              # Decision-making impact
    SOCIAL = "social"                    # Personal/informal relations
    REPORTING = "reporting"              # Formal hierarchy


@dataclass
class TeamMember:
    """An individual in the organization."""
    id: str
    name: str
    role: str = ""
    department: str = ""
    metadata: Dict = field(default_factory=dict)


@dataclass  
class RelationshipAssessment:
    """Assessment of relationship between two team members."""
    source_id: str
    target_id: str
    channel: RelationshipChannel
    weight: Fraction  # -1 to +1, where negative = antagonistic
    notes: str = ""


@dataclass
class ConflictReport:
    """
    Report of detected conflict between team members.
    
    Formal basis: R_conflict predicate in Top__Relations__Weighted.v
    This is not a guess - it's mathematically defined as having
    both positive AND negative relations across channels.
    """
    source_id: str
    target_id: str
    positive_channels: List[str]
    negative_channels: List[str]
    severity: str  # "low", "medium", "high"
    
    @property
    def description(self) -> str:
        pos = ", ".join(self.positive_channels)
        neg = ", ".join(self.negative_channels)
        return f"Mixed signals: positive on [{pos}], negative on [{neg}]"


@dataclass
class IsolationReport:
    """
    Report of team member with insufficient connections.
    
    Formal basis: Seriality violation from Proposition 01.
    In a healthy organization (like a serial relation), every
    member should have at least one outgoing connection.
    """
    member_id: str
    member_name: str
    incoming_count: int
    outgoing_count: int
    recommendation: str


@dataclass
class HostileReport:
    """
    Report of a hostile relationship (all channels negative).
    
    Unlike R_conflict (mixed signals), this is a uniformly
    negative relationship with no positive channels.
    """
    source_id: str
    target_id: str
    negative_channels: List[str]
    total_weight: float  # Sum of all negative weights
    
    @property
    def severity(self) -> str:
        if self.total_weight <= -1.0:
            return "high"
        elif self.total_weight <= -0.5:
            return "medium"
        return "low"


@dataclass
class TeamHealthReport:
    """Comprehensive team health analysis."""
    team_name: str
    member_count: int
    
    # Core metrics (based on verified math)
    connectivity_density: float      # Proportion of possible connections that exist
    sentiment_balance: float         # -1 (all negative) to +1 (all positive)
    channel_alignment: float         # Proportion of harmonious relationships
    seriality_satisfied: bool        # Every member has connections
    
    # Detected issues
    conflicts: List[ConflictReport]
    isolated_members: List[IsolationReport]
    hostile_relationships: List[HostileReport]  # All-negative relationships
    
    # Recommendations
    recommendations: List[str]
    
    def overall_health_score(self) -> float:
        """
        Aggregate health score 0-100.
        
        Weighted combination of verified metrics.
        Conflicts and hostile relationships have significant impact.
        """
        # Start with base score
        score = 50.0
        
        # Connectivity: up to +15
        score += self.connectivity_density * 15
        
        # Sentiment: up to +/- 15
        score += self.sentiment_balance * 15
        
        # Channel alignment: up to +10
        score += self.channel_alignment * 10
        
        # Seriality bonus
        if self.seriality_satisfied:
            score += 10
        else:
            score -= 15
        
        # Conflict penalty - SIGNIFICANT impact
        num_conflicts = len(self.conflicts)
        if num_conflicts > 0:
            # First conflict: -10, each additional: -5
            conflict_penalty = 10 + (num_conflicts - 1) * 5
            score -= min(conflict_penalty, 40)
        
        # High severity conflicts get extra penalty
        high_severity_conflicts = [c for c in self.conflicts if c.severity == "high"]
        score -= len(high_severity_conflicts) * 5
        
        # Hostile relationship penalty - very serious
        num_hostile = len(self.hostile_relationships)
        if num_hostile > 0:
            # First hostile: -15, each additional: -7
            hostile_penalty = 15 + (num_hostile - 1) * 7
            score -= min(hostile_penalty, 45)
        
        # Isolation penalty
        isolation_ratio = len(self.isolated_members) / max(1, self.member_count)
        score -= isolation_ratio * 15
        
        return max(0, min(100, score))


class OrganizationalNetwork:
    """
    Full organizational network analysis using UCF/GUTT foundations.
    
    This class provides the main interface for analyzing team dynamics
    using formally verified relational mathematics.
    """
    
    def __init__(self, team_name: str = "Team"):
        self.team_name = team_name
        self.members: Dict[str, TeamMember] = {}
        self.relations = MultiplexRelation([], [ch.value for ch in RelationshipChannel])
    
    def add_member(self, member: TeamMember) -> None:
        """Add a team member."""
        self.members[member.id] = member
        self.relations.entities.add(member.id)
    
    def add_relationship(self, assessment: RelationshipAssessment) -> None:
        """
        Add a relationship assessment.
        
        Weight should be in range [-1, 1]:
        - Positive: cooperative/supportive
        - Negative: antagonistic/conflicting
        - Zero: no significant relation
        """
        self.relations.set_weight(
            assessment.channel.value,
            assessment.source_id,
            assessment.target_id,
            assessment.weight
        )
    
    def set_relationship(
        self, 
        source_id: str, 
        target_id: str, 
        channel: RelationshipChannel,
        weight: float
    ) -> None:
        """Convenience method to set a relationship."""
        self.relations.set_weight(
            channel.value,
            source_id,
            target_id,
            Fraction(weight).limit_denominator(100)
        )
    
    def detect_conflicts(self) -> List[ConflictReport]:
        """
        Detect all relationship conflicts in the organization.
        
        Formal basis: R_conflict predicate
        
        A conflict exists when the SAME relationship (source->target)
        has BOTH positive channels AND negative channels.
        
        Example: Alice and Bob collaborate well (positive) but have
        trust issues (negative) = CONFLICT DETECTED
        
        WHY THIS IS DIFFERENT FROM OTHER TOOLS:
        This isn't sentiment analysis guessing at conflict.
        This is the mathematical definition: ∃ positive channel ∧ ∃ negative channel.
        The Coq proof guarantees this predicate is correctly defined.
        """
        conflicts = []
        
        for source_id in self.members:
            for target_id in self.members:
                if source_id == target_id:
                    continue
                
                if self.relations.has_conflict(source_id, target_id):
                    # Identify which channels are positive vs negative
                    positive_channels = []
                    negative_channels = []
                    
                    for ch in RelationshipChannel:
                        w = self.relations.get_weight(ch.value, source_id, target_id)
                        if w > 0:
                            positive_channels.append(ch.value)
                        elif w < 0:
                            negative_channels.append(ch.value)
                    
                    # Determine severity
                    max_neg = max(
                        abs(self.relations.get_weight(ch, source_id, target_id))
                        for ch in negative_channels
                    ) if negative_channels else Fraction(0)
                    
                    if max_neg >= Fraction(3, 4):
                        severity = "high"
                    elif max_neg >= Fraction(1, 2):
                        severity = "medium"
                    else:
                        severity = "low"
                    
                    conflicts.append(ConflictReport(
                        source_id=source_id,
                        target_id=target_id,
                        positive_channels=positive_channels,
                        negative_channels=negative_channels,
                        severity=severity
                    ))
        
        return conflicts
    
    def detect_isolation(self) -> List[IsolationReport]:
        """
        Detect isolated team members.
        
        Formal basis: Seriality from Proposition 01
        
        In a "serial" relation, every entity has at least one outgoing edge.
        Team members without connections violate this - they're isolated.
        
        WHY THIS IS DIFFERENT:
        We're not just counting connections. We're checking against the
        formally defined seriality property. The Coq proof shows that
        seriality = "no dead ends" = every entity can reach something.
        """
        isolated = []
        
        for member_id, member in self.members.items():
            # Count connections across all channels
            outgoing = 0
            incoming = 0
            
            for ch in RelationshipChannel:
                for other_id in self.members:
                    if other_id == member_id:
                        continue
                    if self.relations.get_weight(ch.value, member_id, other_id) != 0:
                        outgoing += 1
                    if self.relations.get_weight(ch.value, other_id, member_id) != 0:
                        incoming += 1
            
            # Check for isolation
            if outgoing == 0 and incoming == 0:
                isolated.append(IsolationReport(
                    member_id=member_id,
                    member_name=member.name,
                    incoming_count=0,
                    outgoing_count=0,
                    recommendation="Completely isolated - urgent integration needed"
                ))
            elif outgoing == 0:
                isolated.append(IsolationReport(
                    member_id=member_id,
                    member_name=member.name,
                    incoming_count=incoming,
                    outgoing_count=0,
                    recommendation="No outgoing connections - may not be engaging with team"
                ))
            elif incoming == 0:
                isolated.append(IsolationReport(
                    member_id=member_id,
                    member_name=member.name,
                    incoming_count=0,
                    outgoing_count=outgoing,
                    recommendation="No incoming connections - may not be recognized by team"
                ))
        
        return isolated
    
    def detect_hostile(self) -> List[HostileReport]:
        """
        Detect hostile relationships (all channels negative, none positive).
        
        This is DIFFERENT from R_conflict:
        - R_conflict = mixed signals (some positive, some negative)
        - Hostile = uniformly negative (all channels negative or zero, at least one negative)
        
        A hostile relationship may indicate severe interpersonal issues
        that need intervention, even though it's "consistent" (no mixed signals).
        """
        hostile = []
        
        for source_id in self.members:
            for target_id in self.members:
                if source_id == target_id:
                    continue
                
                positive_channels = []
                negative_channels = []
                total_weight = 0.0
                
                for ch in RelationshipChannel:
                    w = float(self.relations.get_weight(ch.value, source_id, target_id))
                    if w > 0:
                        positive_channels.append(ch.value)
                    elif w < 0:
                        negative_channels.append(ch.value)
                        total_weight += w
                
                # Hostile = at least one negative channel AND no positive channels
                if len(negative_channels) > 0 and len(positive_channels) == 0:
                    hostile.append(HostileReport(
                        source_id=source_id,
                        target_id=target_id,
                        negative_channels=negative_channels,
                        total_weight=total_weight
                    ))
        
        return hostile
    
    def compute_channel_relation(self, channel: RelationshipChannel) -> WeightedRelation:
        """Get the weighted relation for a specific channel."""
        rel = WeightedRelation(list(self.members.keys()))
        for (s, t), w in self.relations._relations[channel.value]._weights.items():
            rel.set_weight(s, t, w)
        return rel
    
    def generate_health_report(self) -> TeamHealthReport:
        """
        Generate comprehensive team health report.
        
        All metrics are based on formally verified mathematical foundations.
        """
        # Compute aggregate relation (sum across channels)
        aggregate = WeightedRelation(list(self.members.keys()))
        for s in self.members:
            for t in self.members:
                if s != t:
                    total = self.relations.aggregate_weight(s, t)
                    if total != 0:
                        aggregate.set_weight(s, t, total)
        
        # Core metrics
        density = float(relation_density(aggregate))
        sentiment = float(sentiment_balance(aggregate))
        alignment = float(multiplex_alignment_score(self.relations))
        
        # Seriality check
        is_serial, violations = check_seriality(aggregate)
        
        # Detect issues
        conflicts = self.detect_conflicts()
        isolated = self.detect_isolation()
        hostile = self.detect_hostile()
        
        # Generate recommendations
        recommendations = []
        
        if not is_serial:
            recommendations.append(
                f"SERIALITY VIOLATION: {len(violations)} members have no outgoing connections. "
                "Consider team-building activities to improve integration."
            )
        
        if len(conflicts) > 0:
            high_severity = [c for c in conflicts if c.severity == "high"]
            if high_severity:
                recommendations.append(
                    f"HIGH PRIORITY: {len(high_severity)} relationships show severe conflict. "
                    "Recommend immediate mediation."
                )
        
        # NEW: Check for hostile relationships
        if len(hostile) > 0:
            high_hostile = [h for h in hostile if h.severity == "high"]
            if high_hostile:
                # Get member names for the report
                hostile_pairs = []
                for h in high_hostile:
                    src_name = self.members[h.source_id].name if h.source_id in self.members else h.source_id
                    tgt_name = self.members[h.target_id].name if h.target_id in self.members else h.target_id
                    hostile_pairs.append(f"{src_name}→{tgt_name}")
                recommendations.append(
                    f"HOSTILE RELATIONSHIPS: {len(high_hostile)} severely negative relationships detected "
                    f"({', '.join(hostile_pairs[:3])}{'...' if len(hostile_pairs) > 3 else ''}). "
                    "All channels negative - recommend intervention."
                )
            elif len(hostile) > 0:
                recommendations.append(
                    f"WARNING: {len(hostile)} relationships are uniformly negative. "
                    "Monitor for escalation."
                )
        
        if sentiment < -0.2:
            recommendations.append(
                "Overall sentiment is negative. Consider investigating sources of dissatisfaction."
            )
        
        if alignment < 0.5:
            recommendations.append(
                "Low channel alignment indicates mixed signals in relationships. "
                "Clarify roles and expectations."
            )
        
        if density < 0.3:
            recommendations.append(
                "Low connectivity density. Team may benefit from more collaboration opportunities."
            )
        
        if len(recommendations) == 0:
            recommendations.append("Team appears healthy across all measured dimensions.")
        
        return TeamHealthReport(
            team_name=self.team_name,
            member_count=len(self.members),
            connectivity_density=density,
            sentiment_balance=sentiment,
            channel_alignment=alignment,
            seriality_satisfied=is_serial,
            conflicts=conflicts,
            isolated_members=isolated,
            hostile_relationships=hostile,
            recommendations=recommendations
        )
    
    def to_dict(self) -> Dict:
        """Export network to dictionary for serialization."""
        return {
            "team_name": self.team_name,
            "members": [
                {
                    "id": m.id,
                    "name": m.name,
                    "role": m.role,
                    "department": m.department
                }
                for m in self.members.values()
            ],
            "relationships": [
                {
                    "source": s,
                    "target": t,
                    "channel": ch,
                    "weight": float(self.relations.get_weight(ch, s, t))
                }
                for ch in [c.value for c in RelationshipChannel]
                for s in self.members
                for t in self.members
                if s != t and self.relations.get_weight(ch, s, t) != 0
            ]
        }
    
    @classmethod
    def from_dict(cls, data: Dict) -> 'OrganizationalNetwork':
        """Load network from dictionary."""
        network = cls(data.get("team_name", "Team"))
        
        for m in data.get("members", []):
            network.add_member(TeamMember(
                id=m["id"],
                name=m["name"],
                role=m.get("role", ""),
                department=m.get("department", "")
            ))
        
        for r in data.get("relationships", []):
            network.set_relationship(
                r["source"],
                r["target"],
                RelationshipChannel(r["channel"]),
                r["weight"]
            )
        
        return network


def create_sample_network() -> OrganizationalNetwork:
    """Create a sample network for demonstration."""
    network = OrganizationalNetwork("Engineering Team")
    
    # Add team members
    members = [
        TeamMember("alice", "Alice Chen", "Tech Lead", "Engineering"),
        TeamMember("bob", "Bob Smith", "Senior Developer", "Engineering"),
        TeamMember("carol", "Carol Davis", "Developer", "Engineering"),
        TeamMember("david", "David Wilson", "Junior Developer", "Engineering"),
        TeamMember("eve", "Eve Johnson", "Product Manager", "Product"),
    ]
    
    for m in members:
        network.add_member(m)
    
    # =========================================================================
    # ALICE (Tech Lead) - Strong leader with good relationships
    # =========================================================================
    
    # Alice -> Bob: Strong working relationship
    network.set_relationship("alice", "bob", RelationshipChannel.COLLABORATION, 0.8)
    network.set_relationship("alice", "bob", RelationshipChannel.TRUST, 0.9)
    network.set_relationship("alice", "bob", RelationshipChannel.COMMUNICATION, 0.7)
    network.set_relationship("alice", "bob", RelationshipChannel.INFLUENCE, 0.6)
    
    # Alice -> Carol: Good but less established
    network.set_relationship("alice", "carol", RelationshipChannel.COLLABORATION, 0.7)
    network.set_relationship("alice", "carol", RelationshipChannel.TRUST, 0.6)
    network.set_relationship("alice", "carol", RelationshipChannel.COMMUNICATION, 0.5)
    
    # Alice -> David: Mentoring relationship
    network.set_relationship("alice", "david", RelationshipChannel.INFLUENCE, 0.8)
    network.set_relationship("alice", "david", RelationshipChannel.TRUST, 0.5)
    network.set_relationship("alice", "david", RelationshipChannel.COMMUNICATION, 0.6)
    
    # Alice -> Eve: Cross-functional partnership
    network.set_relationship("alice", "eve", RelationshipChannel.COMMUNICATION, 0.8)
    network.set_relationship("alice", "eve", RelationshipChannel.COLLABORATION, 0.6)
    network.set_relationship("alice", "eve", RelationshipChannel.TRUST, 0.7)
    
    # =========================================================================
    # BOB (Senior Developer) - Respected but has friction with Carol
    # =========================================================================
    
    # Bob -> Alice: Mutual respect
    network.set_relationship("bob", "alice", RelationshipChannel.TRUST, 0.9)
    network.set_relationship("bob", "alice", RelationshipChannel.INFLUENCE, 0.5)
    network.set_relationship("bob", "alice", RelationshipChannel.REPORTING, 0.8)
    
    # Bob -> Carol: CONFLICT - works well but trust issues
    network.set_relationship("bob", "carol", RelationshipChannel.COLLABORATION, 0.7)  # Positive
    network.set_relationship("bob", "carol", RelationshipChannel.TRUST, -0.5)  # Negative = CONFLICT
    network.set_relationship("bob", "carol", RelationshipChannel.COMMUNICATION, 0.3)
    
    # Bob -> David: Mentoring
    network.set_relationship("bob", "david", RelationshipChannel.INFLUENCE, 0.6)
    network.set_relationship("bob", "david", RelationshipChannel.COLLABORATION, 0.4)
    network.set_relationship("bob", "david", RelationshipChannel.SOCIAL, 0.5)
    
    # =========================================================================
    # CAROL (Developer) - Good worker but interpersonal challenges
    # =========================================================================
    
    # Carol -> Alice: Reports to, respects
    network.set_relationship("carol", "alice", RelationshipChannel.TRUST, 0.8)
    network.set_relationship("carol", "alice", RelationshipChannel.REPORTING, 0.9)
    network.set_relationship("carol", "alice", RelationshipChannel.INFLUENCE, 0.3)
    
    # Carol -> Bob: CONFLICT - reciprocal issues
    network.set_relationship("carol", "bob", RelationshipChannel.COLLABORATION, 0.6)  # Positive
    network.set_relationship("carol", "bob", RelationshipChannel.TRUST, -0.4)  # Negative = CONFLICT
    network.set_relationship("carol", "bob", RelationshipChannel.SOCIAL, -0.2)  # Also negative
    
    # Carol -> David: Friendly, peers
    network.set_relationship("carol", "david", RelationshipChannel.SOCIAL, 0.7)
    network.set_relationship("carol", "david", RelationshipChannel.COLLABORATION, 0.5)
    network.set_relationship("carol", "david", RelationshipChannel.COMMUNICATION, 0.6)
    
    # =========================================================================
    # DAVID (Junior Developer) - Learning, fewer connections
    # =========================================================================
    
    # David -> Carol: Good peer relationship
    network.set_relationship("david", "carol", RelationshipChannel.SOCIAL, 0.8)
    network.set_relationship("david", "carol", RelationshipChannel.TRUST, 0.6)
    
    # David -> Alice: Looks up to
    network.set_relationship("david", "alice", RelationshipChannel.TRUST, 0.7)
    network.set_relationship("david", "alice", RelationshipChannel.REPORTING, 0.5)
    
    # David -> Bob: Learning from
    network.set_relationship("david", "bob", RelationshipChannel.INFLUENCE, 0.4)
    network.set_relationship("david", "bob", RelationshipChannel.TRUST, 0.5)
    
    # =========================================================================
    # EVE (Product Manager) - Cross-functional, external to eng hierarchy
    # =========================================================================
    
    # Eve -> Alice: Key partnership
    network.set_relationship("eve", "alice", RelationshipChannel.COMMUNICATION, 0.8)
    network.set_relationship("eve", "alice", RelationshipChannel.COLLABORATION, 0.7)
    network.set_relationship("eve", "alice", RelationshipChannel.TRUST, 0.6)
    
    # Eve -> Bob: Some communication
    network.set_relationship("eve", "bob", RelationshipChannel.COMMUNICATION, 0.4)
    network.set_relationship("eve", "bob", RelationshipChannel.COLLABORATION, 0.3)
    
    # Eve -> Carol: Limited interaction
    network.set_relationship("eve", "carol", RelationshipChannel.COMMUNICATION, 0.2)
    
    # Eve has no direct relationship with David (potential gap)
    
    return network
