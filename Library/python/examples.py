#!/usr/bin/env python3
"""
UCF Extensions - Example Usage
==============================

Demonstrates the core concepts from the Coq library in Python.
"""

from ucf_extensions import (
    Whole, Elem, WholeCompletion, SerialExtension,
    IteratedCompletion, RelationGraph, lift, complete
)

# =============================================================================
#                       EXAMPLE 1: Basic Whole Completion
# =============================================================================

print("=" * 60)
print("EXAMPLE 1: Basic Whole Completion")
print("=" * 60)

# The natural numbers with < relation have dead ends (no successor for max)
# With Whole completion, every number relates to Whole

wc = WholeCompletion[int]()

# Lift the less-than relation
lt = wc.lift(lambda a, b: a < b)

# Test between elements (conservative - matches base relation)
print(f"5 < 10: {lt(wc.elem(5), wc.elem(10))}")      # True
print(f"10 < 5: {lt(wc.elem(10), wc.elem(5))}")      # False

# SERIALITY: Everything relates to Whole
print(f"5 → Whole: {lt(wc.elem(5), wc.whole)}")      # True
print(f"1000000 → Whole: {lt(wc.elem(1000000), wc.whole)}")  # True

# TERMINAL: Whole only relates to itself
print(f"Whole → 5: {lt(wc.whole, wc.elem(5))}")      # False
print(f"Whole → Whole: {lt(wc.whole, wc.whole)}")    # True

print()

# =============================================================================
#                       EXAMPLE 2: Empty Relation Made Serial
# =============================================================================

print("=" * 60)
print("EXAMPLE 2: Empty Relation Becomes Serial")
print("=" * 60)

# Even the empty relation (nothing relates to anything) becomes serial
empty = wc.lift(lambda a, b: False)

print(f"1 → 2 (empty): {empty(wc.elem(1), wc.elem(2))}")   # False
print(f"1 → 1 (empty): {empty(wc.elem(1), wc.elem(1))}")   # False
print(f"1 → Whole: {empty(wc.elem(1), wc.whole)}")          # True! (seriality)

print()

# =============================================================================
#                       EXAMPLE 3: Serial Extension with Tracking
# =============================================================================

print("=" * 60)
print("EXAMPLE 3: Serial Extension with Graph")
print("=" * 60)

# Create an extension with explicit elements
ext = SerialExtension[str]()
ext.add("alice")
ext.add("bob")
ext.add("carol")

# Register a "knows" relation
knows_base = {
    ("alice", "bob"),
    ("bob", "carol"),
}
knows = ext.register_relation("knows", lambda a, b: (a, b) in knows_base)

# List all successors
print("Successors under 'knows':")
for person in ["alice", "bob", "carol"]:
    succs = list(ext.successors(ext.elem(person), "knows"))
    print(f"  {person} → {[str(s) for s in succs]}")

# Note: everyone has Whole as a successor!

# Path checking
print(f"\nPath alice → carol: {ext.has_path(ext.elem('alice'), ext.elem('carol'), 'knows')}")
print(f"Path carol → alice: {ext.has_path(ext.elem('carol'), ext.elem('alice'), 'knows')}")
print(f"Path carol → Whole: {ext.has_path(ext.elem('carol'), ext.whole, 'knows')}")  # Always True

print()

# =============================================================================
#                       EXAMPLE 4: Verify Seriality
# =============================================================================

print("=" * 60)
print("EXAMPLE 4: Seriality Verification")
print("=" * 60)

graph = RelationGraph(ext, "knows")

print(f"Edge count: {graph.edge_count()}")
print(f"Seriality verified: {graph.verify_seriality()}")  # Always True!

print("\nAdjacency list:")
for node, neighbors in graph.to_dict().items():
    print(f"  {node}: {neighbors}")

print()

# =============================================================================
#                       EXAMPLE 5: Iterated Completion (Nested Wholes)
# =============================================================================

print("=" * 60)
print("EXAMPLE 5: Iterated Completion (Fractal Structure)")
print("=" * 60)

# Double completion: U + {Whole₀} + {Whole₁}
double = IteratedCompletion[int](depth=2)

print(f"Depth: {double.depth}")
print(f"Inject 42: {double.inject(42)}")
print(f"Whole at level 0 (outer): {double.whole_at_level(0)}")
print(f"Whole at level 1 (inner): {double.whole_at_level(1)}")

print("\nAll Wholes:")
for i, w in enumerate(double.all_wholes()):
    print(f"  Level {i}: {w}")

print()

# =============================================================================
#                       EXAMPLE 6: Quick Construction
# =============================================================================

print("=" * 60)
print("EXAMPLE 6: Quick Construction")
print("=" * 60)

# One-liner to create a serial extension
ext = complete({1, 2, 3, 4, 5}, lambda a, b: a % 2 == b % 2)  # Same parity

rel = ext.get_relation("R")
print("Same parity relation:")
print(f"  1 ~ 3: {rel(ext.elem(1), ext.elem(3))}")   # True (both odd)
print(f"  1 ~ 2: {rel(ext.elem(1), ext.elem(2))}")   # False
print(f"  2 ~ 4: {rel(ext.elem(2), ext.elem(4))}")   # True (both even)
print(f"  5 → Whole: {rel(ext.elem(5), ext.whole)}")  # True (seriality)

print()

# =============================================================================
#                       EXAMPLE 7: Divisibility Relation
# =============================================================================

print("=" * 60)
print("EXAMPLE 7: Divisibility with Whole")
print("=" * 60)

wc = WholeCompletion[int]()
divides = wc.lift(lambda a, b: b % a == 0 if a != 0 else False)

print("Divisibility:")
print(f"  2 | 6: {divides(wc.elem(2), wc.elem(6))}")    # True
print(f"  3 | 7: {divides(wc.elem(3), wc.elem(7))}")    # False
print(f"  7 | 1: {divides(wc.elem(7), wc.elem(1))}")    # False

# Prime numbers have no non-trivial divisors...
# But they still relate to Whole!
print(f"\n  7 → Whole: {divides(wc.elem(7), wc.whole)}")  # True

print()

# =============================================================================
#                       EXAMPLE 8: Type Safety with Generics
# =============================================================================

print("=" * 60)
print("EXAMPLE 8: Different Types")
print("=" * 60)

# Works with any type
string_wc = WholeCompletion[str]()
is_prefix = string_wc.lift(lambda a, b: b.startswith(a))

print("Prefix relation:")
print(f"  'hello' prefix of 'hello world': {is_prefix(string_wc.elem('hello'), string_wc.elem('hello world'))}")
print(f"  'world' prefix of 'hello world': {is_prefix(string_wc.elem('world'), string_wc.elem('hello world'))}")
print(f"  'xyz' → Whole: {is_prefix(string_wc.elem('xyz'), string_wc.whole)}")

print()

# =============================================================================
#                       EXAMPLE 9: The Core Theorem
# =============================================================================

print("=" * 60)
print("THE CORE THEOREM")
print("=" * 60)

print("""
For ANY relation R on ANY set U:
  
  1. SERIALITY: ∀x. R'(x, Whole)
     Every element relates to Whole.
     
  2. CONSERVATIVITY: R'(Elem(a), Elem(b)) ↔ R(a, b)
     The lifted relation agrees with R on base elements.
     
  3. FRESHNESS: ∀u. Elem(u) ≠ Whole
     Whole is genuinely new.
     
  4. TERMINAL: ∀u. ¬R'(Whole, Elem(u))
     Whole only relates to itself.

This is proven with ZERO AXIOMS in the Coq library.
The Python implementation mirrors these semantics.
""")

print("=" * 60)
print("All examples completed successfully!")
print("=" * 60)
