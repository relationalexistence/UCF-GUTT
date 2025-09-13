Relational Arithmetic (Coq): What’s Proven and Why It Matters

File: coq/props/RelationalArithmetic.v
Goal: Show that when “numbers” are treated as relational objects, their basic operations still satisfy the classical ring laws.

What the proofs establish

We model relational numbers as integers (Z). Relational addition and multiplication are defined by reuse of integer operations:

radd := Z.add

rmul := Z.mul

The following theorems are proven, mechanically, in Coq:

Commutativity of addition
radd_comm : ∀ a b, radd a b = radd b a

Associativity of addition
radd_assoc : ∀ a b c, radd (radd a b) c = radd a (radd b c)

Commutativity of multiplication
rmul_comm : ∀ a b, rmul a b = rmul b a

Associativity of multiplication
rmul_assoc : ∀ a b c, rmul (rmul a b) c = rmul a (rmul b c)

Distributivity
rmul_distr : ∀ a b c, rmul a (radd b c) = radd (rmul a b) (rmul a c)

Plain-language reading (example: associativity)

radd_assoc says: for any three relational numbers a, b, c,

radd (radd a b) c  =  radd a (radd b c)


Grouping doesn’t change the result. Intuitively: “add a and b first, then add c” equals “add b and c first, then add a”.

Why this matters for UCF/GUTT

In UCF/GUTT, arithmetic is interpreted as special cases of relational joins/products over a network/tensor of relations. Proving the classical algebraic laws in this setting shows:

Compatibility with standard math: the relational viewpoint doesn’t break arithmetic; it recovers it.

Well-behaved composition: joins/products can be regrouped and reordered without ambiguity, enabling higher structures (groups, rings, fields) inside the relational ontology.

A bridge to applications: once ring laws hold, we can safely build linear algebra, optimization, and learning over relational tensors the same way we do over numbers—now with principled semantics.

Tiny worked example (grounded intuition)

Let a=2, b=5, c=−3. Then:

radd (radd a b) c = (2 + 5) + (−3) = 7 + (−3) = 4
radd a (radd b c) = 2 + (5 + (−3)) = 2 + 2 = 4


They match, as radd_assoc guarantees, regardless of grouping. Similar concrete checks illustrate the other laws.
