# UCF Extensions - Python

**Zero-axiom universal connectivity for any relation.**

A Python implementation of the machine-verified Coq proofs from the UCF/GUTT Extensions Library.

## Core Idea

Any relation R on any set U can be made **serial** (no dead ends) by adding a single element called **Whole**. This isn't an axiom—it's a constructive theorem proven with zero assumptions.

```python
from ucf_extensions import WholeCompletion, Elem, Whole

# Natural numbers with < have dead ends (what's after the maximum?)
wc = WholeCompletion()
lt = wc.lift(lambda a, b: a < b)

# Between elements: works like normal
lt(Elem(5), Elem(10))   # True (5 < 10)
lt(Elem(10), Elem(5))   # False

# But now EVERY element has a successor
lt(Elem(999999), Whole)  # True - even huge numbers relate to Whole
lt(Elem(0), Whole)       # True
lt(Whole, Whole)         # True - Whole relates to itself
lt(Whole, Elem(5))       # False - Whole is terminal
```

## Key Properties

All of these are **proven in Coq** (see `Library/src/`):

| Property | Meaning | Coq Lemma |
|----------|---------|-----------|
| **Seriality** | ∀x. R'(x, Whole) | `WholeCompletion.serial` |
| **Conservativity** | R'(Elem a, Elem b) ↔ R(a,b) | `WholeCompletion.lift_conservative` |
| **Freshness** | Elem(u) ≠ Whole | `WholeCompletion.point_fresh` |
| **Terminal** | ¬R'(Whole, Elem u) | `WholeCompletion.point_terminal` |

## Installation

```bash
pip install ucf-extensions
```

Or from source:
```bash
git clone https://github.com/relationalexistence/UCF-GUTT
cd UCF-GUTT/Library/python
pip install -e .
```

## Quick Examples

### Empty relation becomes serial
```python
from ucf_extensions import lift, Elem, Whole

# Nothing relates to anything
empty = lift(lambda a, b: False)

empty(Elem(1), Elem(2))  # False
empty(Elem(1), Whole)    # True! (seriality)
```

### Graph with universal sink
```python
from ucf_extensions import SerialExtension

ext = SerialExtension()
ext.add("alice")
ext.add("bob")
ext.add("carol")

# Define who knows whom
knows_pairs = {("alice", "bob"), ("bob", "carol")}
ext.register_relation("knows", lambda a, b: (a, b) in knows_pairs)

# Carol has no outgoing edges... except to Whole
list(ext.successors(ext.elem("carol"), "knows"))
# [Whole]
```

### Nested completion (fractal structure)
```python
from ucf_extensions import IteratedCompletion

# Two levels of Whole
double = IteratedCompletion(depth=2)

double.inject(42)           # Elem(Elem(42))
double.whole_at_level(0)    # Elem(Whole) - outer
double.whole_at_level(1)    # Whole - inner
```

## API Reference

### Core Types

- `Whole` - The universal sink element
- `Elem(value)` - Embed a value into the carrier
- `Carrier` - Base type for Whole and Elem

### Main Classes

- `WholeCompletion[T]()` - Create a completion
  - `.elem(v)` - Embed value
  - `.whole` - The Whole element
  - `.lift(relation)` - Lift a relation

- `LiftedRelation[T]` - A serial relation
  - `(x, y)` - Evaluate relation
  - `.base` - Original relation

- `SerialExtension[T]` - Tracked elements + relations
  - `.add(v)` - Add element
  - `.register_relation(name, rel)` - Register relation
  - `.successors(x, name)` - Find successors
  - `.has_path(start, end, name)` - Path exists?

- `IteratedCompletion[T](depth)` - Nested Wholes
  - `.inject(v)` - Embed at deepest level
  - `.whole_at_level(n)` - Whole at level n

### Convenience Functions

- `lift(relation)` - Quick lift without creating WholeCompletion
- `complete(elements, relation)` - One-liner extension

## Mathematical Foundation

This library implements the constructions from:

> **Universal Connectivity via Whole-Completion: A Zero-Axiom Proof**
> 
> The option type construction `U → option U` with `None` as "Whole" provides
> a constructive proof that any relation can be extended to a serial relation.
> Verified in Coq with 0 axioms, 0 admits, 163 machine-checked exports.

The Coq source is at `Library/src/Top__Extensions__*.v`

## License

UCF/GUTT Research & Evaluation License v1.1 (Non-Commercial, No Derivatives)

© 2023-2025 Michael Fillippini. All Rights Reserved.
