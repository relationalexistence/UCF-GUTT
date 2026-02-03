"""
Unit Tests for UCF/GUTT Core Relational Mathematics
=====================================================

Tests covering:
- Conflict detection predicates (R_conflict)
- Harmony detection predicates (R_harmony)
- Support predicates (R_support)
- Seriality checking
- Multiplex aggregation
- Edge cases and boundary conditions

Copyright (C) 2023-2026 Michael Fillippini. All Rights Reserved.
"""

import unittest
from fractions import Fraction
import sys
import os

# Add parent directory to path for imports
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from ucf_core import (
    WeightedRelation,
    WeightedEdge,
    MultiplexRelation,
    RelationSign,
    check_seriality,
    ensure_seriality,
    relation_density,
    sentiment_balance,
    multiplex_alignment_score
)


class TestRelationSign(unittest.TestCase):
    """Test RelationSign enum behavior."""
    
    def test_sign_values(self):
        """Verify sign enum values match formal specification."""
        self.assertEqual(RelationSign.POSITIVE.value, 1)
        self.assertEqual(RelationSign.ZERO.value, 0)
        self.assertEqual(RelationSign.NEGATIVE.value, -1)


class TestWeightedEdge(unittest.TestCase):
    """Test WeightedEdge dataclass and properties."""
    
    def test_positive_edge(self):
        """Test positive weight edge classification."""
        edge = WeightedEdge("a", "b", Fraction(3, 4))
        self.assertEqual(edge.sign, RelationSign.POSITIVE)
        self.assertEqual(edge.magnitude, Fraction(3, 4))
        self.assertTrue(edge.has_support)
    
    def test_negative_edge(self):
        """Test negative weight edge classification."""
        edge = WeightedEdge("a", "b", Fraction(-1, 2))
        self.assertEqual(edge.sign, RelationSign.NEGATIVE)
        self.assertEqual(edge.magnitude, Fraction(1, 2))
        self.assertTrue(edge.has_support)
    
    def test_zero_edge(self):
        """Test zero weight edge (no relation)."""
        edge = WeightedEdge("a", "b", Fraction(0))
        self.assertEqual(edge.sign, RelationSign.ZERO)
        self.assertEqual(edge.magnitude, Fraction(0))
        self.assertFalse(edge.has_support)
    
    def test_small_positive(self):
        """Test very small positive weight."""
        edge = WeightedEdge("a", "b", Fraction(1, 1000000))
        self.assertEqual(edge.sign, RelationSign.POSITIVE)
        self.assertTrue(edge.has_support)
    
    def test_small_negative(self):
        """Test very small negative weight."""
        edge = WeightedEdge("a", "b", Fraction(-1, 1000000))
        self.assertEqual(edge.sign, RelationSign.NEGATIVE)
        self.assertTrue(edge.has_support)


class TestWeightedRelation(unittest.TestCase):
    """Test WeightedRelation class."""
    
    def setUp(self):
        """Set up test relation."""
        self.rel = WeightedRelation(["a", "b", "c"])
    
    def test_initial_state(self):
        """Test initial empty relation."""
        self.assertEqual(len(self.rel.entities), 3)
        self.assertEqual(self.rel.get_weight("a", "b"), Fraction(0))
    
    def test_set_and_get_weight(self):
        """Test setting and retrieving weights."""
        self.rel.set_weight("a", "b", Fraction(1, 2))
        self.assertEqual(self.rel.get_weight("a", "b"), Fraction(1, 2))
        # Reverse direction should still be 0
        self.assertEqual(self.rel.get_weight("b", "a"), Fraction(0))
    
    def test_support_predicate(self):
        """Test R_support predicate."""
        self.rel.set_weight("a", "b", Fraction(1, 2))
        self.assertTrue(self.rel.has_support("a", "b"))
        self.assertFalse(self.rel.has_support("b", "a"))
        self.assertFalse(self.rel.has_support("a", "c"))
    
    def test_positive_predicate(self):
        """Test R_pos predicate."""
        self.rel.set_weight("a", "b", Fraction(1, 2))
        self.rel.set_weight("a", "c", Fraction(-1, 2))
        self.assertTrue(self.rel.is_positive("a", "b"))
        self.assertFalse(self.rel.is_positive("a", "c"))
    
    def test_negative_predicate(self):
        """Test R_neg predicate."""
        self.rel.set_weight("a", "b", Fraction(1, 2))
        self.rel.set_weight("a", "c", Fraction(-1, 2))
        self.assertFalse(self.rel.is_negative("a", "b"))
        self.assertTrue(self.rel.is_negative("a", "c"))
    
    def test_all_edges(self):
        """Test retrieving all edges."""
        self.rel.set_weight("a", "b", Fraction(1, 2))
        self.rel.set_weight("b", "c", Fraction(-1, 3))
        edges = self.rel.all_edges()
        self.assertEqual(len(edges), 2)
    
    def test_outgoing_edges(self):
        """Test retrieving outgoing edges."""
        self.rel.set_weight("a", "b", Fraction(1, 2))
        self.rel.set_weight("a", "c", Fraction(1, 3))
        self.rel.set_weight("b", "c", Fraction(1, 4))
        
        outgoing_a = self.rel.outgoing("a")
        self.assertEqual(len(outgoing_a), 2)
        
        outgoing_b = self.rel.outgoing("b")
        self.assertEqual(len(outgoing_b), 1)
    
    def test_incoming_edges(self):
        """Test retrieving incoming edges."""
        self.rel.set_weight("a", "b", Fraction(1, 2))
        self.rel.set_weight("c", "b", Fraction(1, 3))
        
        incoming_b = self.rel.incoming("b")
        self.assertEqual(len(incoming_b), 2)
        
        incoming_a = self.rel.incoming("a")
        self.assertEqual(len(incoming_a), 0)


class TestMultiplexRelation(unittest.TestCase):
    """Test MultiplexRelation class - the core for conflict/harmony detection."""
    
    def setUp(self):
        """Set up test multiplex relation."""
        self.channels = ["trade", "military", "diplomatic"]
        self.mpx = MultiplexRelation(["A", "B", "C"], self.channels)
    
    def test_initial_state(self):
        """Test initial multiplex state."""
        self.assertEqual(len(self.mpx.channels), 3)
        self.assertEqual(self.mpx.get_weight("trade", "A", "B"), Fraction(0))
    
    def test_set_and_get_channel_weight(self):
        """Test setting weights on specific channels."""
        self.mpx.set_weight("trade", "A", "B", Fraction(7, 10))
        self.assertEqual(self.mpx.get_weight("trade", "A", "B"), Fraction(7, 10))
        self.assertEqual(self.mpx.get_weight("military", "A", "B"), Fraction(0))


class TestConflictPredicate(unittest.TestCase):
    """
    Test R_conflict predicate.
    
    Formal definition from Coq:
        R_conflict M channels a b :=
          (exists k1, In k1 channels AND R_pos (M k1) a b) AND
          (exists k2, In k2 channels AND R_neg (M k2) a b)
    
    In plain English: conflict exists when there's at least one positive
    channel AND at least one negative channel between the same pair.
    """
    
    def setUp(self):
        """Set up multiplex for conflict tests."""
        self.channels = ["collab", "trust", "social"]
        self.mpx = MultiplexRelation(["A", "B"], self.channels)
    
    def test_no_conflict_all_positive(self):
        """All positive channels = no conflict."""
        self.mpx.set_weight("collab", "A", "B", Fraction(7, 10))
        self.mpx.set_weight("trust", "A", "B", Fraction(5, 10))
        self.mpx.set_weight("social", "A", "B", Fraction(3, 10))
        
        self.assertFalse(self.mpx.has_conflict("A", "B"))
    
    def test_no_conflict_all_negative(self):
        """All negative channels = no conflict (just antagonistic)."""
        self.mpx.set_weight("collab", "A", "B", Fraction(-7, 10))
        self.mpx.set_weight("trust", "A", "B", Fraction(-5, 10))
        self.mpx.set_weight("social", "A", "B", Fraction(-3, 10))
        
        self.assertFalse(self.mpx.has_conflict("A", "B"))
    
    def test_no_conflict_all_zero(self):
        """No relations = no conflict."""
        self.assertFalse(self.mpx.has_conflict("A", "B"))
    
    def test_conflict_positive_and_negative(self):
        """Mixed signals = conflict detected."""
        self.mpx.set_weight("collab", "A", "B", Fraction(7, 10))   # positive
        self.mpx.set_weight("trust", "A", "B", Fraction(-5, 10))   # negative
        
        self.assertTrue(self.mpx.has_conflict("A", "B"))
    
    def test_conflict_with_zeros(self):
        """Conflict with some zero channels."""
        self.mpx.set_weight("collab", "A", "B", Fraction(7, 10))   # positive
        self.mpx.set_weight("trust", "A", "B", Fraction(0))        # zero
        self.mpx.set_weight("social", "A", "B", Fraction(-3, 10))  # negative
        
        self.assertTrue(self.mpx.has_conflict("A", "B"))
    
    def test_conflict_minimal(self):
        """Minimal conflict: one positive, one negative."""
        self.mpx.set_weight("collab", "A", "B", Fraction(1, 1000))   # tiny positive
        self.mpx.set_weight("trust", "A", "B", Fraction(-1, 1000))   # tiny negative
        
        self.assertTrue(self.mpx.has_conflict("A", "B"))
    
    def test_conflict_is_directional(self):
        """Conflict is checked per direction."""
        self.mpx.set_weight("collab", "A", "B", Fraction(7, 10))
        self.mpx.set_weight("trust", "A", "B", Fraction(-5, 10))
        # A→B has conflict
        
        self.mpx.set_weight("collab", "B", "A", Fraction(5, 10))
        self.mpx.set_weight("trust", "B", "A", Fraction(3, 10))
        # B→A is all positive
        
        self.assertTrue(self.mpx.has_conflict("A", "B"))
        self.assertFalse(self.mpx.has_conflict("B", "A"))


class TestHarmonyPredicate(unittest.TestCase):
    """
    Test R_harmony predicate.
    
    Harmony means all non-zero channels have the same sign
    (either all positive or all negative).
    """
    
    def setUp(self):
        """Set up multiplex for harmony tests."""
        self.channels = ["collab", "trust", "social"]
        self.mpx = MultiplexRelation(["A", "B"], self.channels)
    
    def test_harmony_all_positive(self):
        """All positive = harmony."""
        self.mpx.set_weight("collab", "A", "B", Fraction(7, 10))
        self.mpx.set_weight("trust", "A", "B", Fraction(5, 10))
        self.mpx.set_weight("social", "A", "B", Fraction(3, 10))
        
        self.assertTrue(self.mpx.has_harmony("A", "B"))
    
    def test_harmony_all_negative(self):
        """All negative = harmony (aligned antagonism)."""
        self.mpx.set_weight("collab", "A", "B", Fraction(-7, 10))
        self.mpx.set_weight("trust", "A", "B", Fraction(-5, 10))
        
        self.assertTrue(self.mpx.has_harmony("A", "B"))
    
    def test_harmony_positive_with_zeros(self):
        """Positive channels with zeros = still harmony."""
        self.mpx.set_weight("collab", "A", "B", Fraction(7, 10))
        self.mpx.set_weight("trust", "A", "B", Fraction(0))
        self.mpx.set_weight("social", "A", "B", Fraction(3, 10))
        
        self.assertTrue(self.mpx.has_harmony("A", "B"))
    
    def test_harmony_all_zero(self):
        """All zero = vacuously harmonious."""
        self.assertTrue(self.mpx.has_harmony("A", "B"))
    
    def test_no_harmony_mixed(self):
        """Mixed signals = no harmony."""
        self.mpx.set_weight("collab", "A", "B", Fraction(7, 10))
        self.mpx.set_weight("trust", "A", "B", Fraction(-5, 10))
        
        self.assertFalse(self.mpx.has_harmony("A", "B"))
    
    def test_conflict_and_harmony_mutually_exclusive(self):
        """R_conflict and R_harmony should never both be True."""
        # Case 1: Conflict scenario
        self.mpx.set_weight("collab", "A", "B", Fraction(7, 10))
        self.mpx.set_weight("trust", "A", "B", Fraction(-5, 10))
        
        has_conflict = self.mpx.has_conflict("A", "B")
        has_harmony = self.mpx.has_harmony("A", "B")
        
        # Cannot have both
        self.assertFalse(has_conflict and has_harmony)
        
        # Reset
        self.mpx.set_weight("trust", "A", "B", Fraction(5, 10))
        
        # Case 2: Harmony scenario
        has_conflict = self.mpx.has_conflict("A", "B")
        has_harmony = self.mpx.has_harmony("A", "B")
        
        self.assertFalse(has_conflict and has_harmony)
        self.assertTrue(has_harmony)


class TestSeriality(unittest.TestCase):
    """
    Test seriality checking (Proposition 01).
    
    Seriality: Every entity has at least one outgoing edge.
    """
    
    def test_serial_relation(self):
        """Test relation that satisfies seriality."""
        rel = WeightedRelation(["a", "b", "c"])
        rel.set_weight("a", "b", Fraction(1))
        rel.set_weight("b", "c", Fraction(1))
        rel.set_weight("c", "a", Fraction(1))
        
        is_serial, violations = check_seriality(rel)
        self.assertTrue(is_serial)
        self.assertEqual(len(violations), 0)
    
    def test_non_serial_relation(self):
        """Test relation that violates seriality."""
        rel = WeightedRelation(["a", "b", "c"])
        rel.set_weight("a", "b", Fraction(1))
        rel.set_weight("b", "a", Fraction(1))
        # 'c' has no outgoing edges
        
        is_serial, violations = check_seriality(rel)
        self.assertFalse(is_serial)
        self.assertIn("c", violations)
    
    def test_ensure_seriality(self):
        """Test WholeCompletion ensures seriality."""
        rel = WeightedRelation(["a", "b", "c"])
        rel.set_weight("a", "b", Fraction(1))
        # 'b' and 'c' have no outgoing
        
        is_serial, _ = check_seriality(rel)
        self.assertFalse(is_serial)
        
        # Apply WholeCompletion
        ensure_seriality(rel)
        
        is_serial, violations = check_seriality(rel)
        self.assertTrue(is_serial)
        self.assertEqual(len(violations), 0)


class TestAggregateMetrics(unittest.TestCase):
    """Test aggregate metric functions."""
    
    def test_relation_density_empty(self):
        """Density of empty relation."""
        rel = WeightedRelation(["a", "b", "c"])
        density = relation_density(rel)
        self.assertEqual(density, Fraction(0))
    
    def test_relation_density_full(self):
        """Density of fully connected relation."""
        rel = WeightedRelation(["a", "b", "c"])
        for s in ["a", "b", "c"]:
            for t in ["a", "b", "c"]:
                if s != t:
                    rel.set_weight(s, t, Fraction(1))
        
        density = relation_density(rel)
        self.assertEqual(density, Fraction(1))  # 6/6 = 1
    
    def test_relation_density_partial(self):
        """Density of partially connected relation."""
        rel = WeightedRelation(["a", "b", "c"])
        rel.set_weight("a", "b", Fraction(1))
        rel.set_weight("b", "c", Fraction(1))
        rel.set_weight("c", "a", Fraction(1))
        
        density = relation_density(rel)
        self.assertEqual(density, Fraction(3, 6))  # 3 edges, 6 possible
    
    def test_sentiment_balance_all_positive(self):
        """Sentiment of all positive relations."""
        rel = WeightedRelation(["a", "b"])
        rel.set_weight("a", "b", Fraction(1))
        rel.set_weight("b", "a", Fraction(1))
        
        sentiment = sentiment_balance(rel)
        self.assertEqual(sentiment, Fraction(1))
    
    def test_sentiment_balance_all_negative(self):
        """Sentiment of all negative relations."""
        rel = WeightedRelation(["a", "b"])
        rel.set_weight("a", "b", Fraction(-1))
        rel.set_weight("b", "a", Fraction(-1))
        
        sentiment = sentiment_balance(rel)
        self.assertEqual(sentiment, Fraction(-1))
    
    def test_sentiment_balance_mixed(self):
        """Sentiment of mixed relations."""
        rel = WeightedRelation(["a", "b"])
        rel.set_weight("a", "b", Fraction(1))    # +1
        rel.set_weight("b", "a", Fraction(-1))   # -1
        
        sentiment = sentiment_balance(rel)
        self.assertEqual(sentiment, Fraction(0))  # Balanced
    
    def test_multiplex_alignment_score(self):
        """Test alignment score for multiplex relation."""
        channels = ["c1", "c2"]
        mpx = MultiplexRelation(["a", "b", "c"], channels)
        
        # a→b: all positive (harmony)
        mpx.set_weight("c1", "a", "b", Fraction(1))
        mpx.set_weight("c2", "a", "b", Fraction(1))
        
        # b→c: mixed (conflict)
        mpx.set_weight("c1", "b", "c", Fraction(1))
        mpx.set_weight("c2", "b", "c", Fraction(-1))
        
        score = multiplex_alignment_score(mpx)
        # 1 harmony, 1 conflict out of 2 with relations
        self.assertEqual(score, Fraction(1, 2))


class TestConflictPairs(unittest.TestCase):
    """Test conflict_pairs method."""
    
    def test_find_all_conflicts(self):
        """Test finding all conflict pairs."""
        channels = ["c1", "c2"]
        mpx = MultiplexRelation(["a", "b", "c"], channels)
        
        # a→b: conflict
        mpx.set_weight("c1", "a", "b", Fraction(1))
        mpx.set_weight("c2", "a", "b", Fraction(-1))
        
        # b→c: conflict
        mpx.set_weight("c1", "b", "c", Fraction(1))
        mpx.set_weight("c2", "b", "c", Fraction(-1))
        
        # a→c: harmony
        mpx.set_weight("c1", "a", "c", Fraction(1))
        mpx.set_weight("c2", "a", "c", Fraction(1))
        
        conflicts = mpx.conflict_pairs()
        self.assertEqual(len(conflicts), 2)
        self.assertIn(("a", "b"), conflicts)
        self.assertIn(("b", "c"), conflicts)


class TestHarmonyPairs(unittest.TestCase):
    """Test harmony_pairs method."""
    
    def test_find_all_harmonies(self):
        """Test finding all harmony pairs."""
        channels = ["c1", "c2"]
        mpx = MultiplexRelation(["a", "b", "c"], channels)
        
        # a→b: harmony (all positive)
        mpx.set_weight("c1", "a", "b", Fraction(1))
        mpx.set_weight("c2", "a", "b", Fraction(1))
        
        # b→c: conflict
        mpx.set_weight("c1", "b", "c", Fraction(1))
        mpx.set_weight("c2", "b", "c", Fraction(-1))
        
        # a→c: harmony (all negative)
        mpx.set_weight("c1", "a", "c", Fraction(-1))
        mpx.set_weight("c2", "a", "c", Fraction(-1))
        
        harmonies = mpx.harmony_pairs()
        self.assertEqual(len(harmonies), 2)
        self.assertIn(("a", "b"), harmonies)
        self.assertIn(("a", "c"), harmonies)


class TestAggregateWeight(unittest.TestCase):
    """Test aggregate_weight method."""
    
    def test_aggregate_weight(self):
        """Test summing weights across channels."""
        channels = ["c1", "c2", "c3"]
        mpx = MultiplexRelation(["a", "b"], channels)
        
        mpx.set_weight("c1", "a", "b", Fraction(1, 2))
        mpx.set_weight("c2", "a", "b", Fraction(1, 4))
        mpx.set_weight("c3", "a", "b", Fraction(-1, 4))
        
        total = mpx.aggregate_weight("a", "b")
        self.assertEqual(total, Fraction(1, 2))  # 0.5 + 0.25 - 0.25 = 0.5


if __name__ == "__main__":
    # Run with verbose output
    unittest.main(verbosity=2)
