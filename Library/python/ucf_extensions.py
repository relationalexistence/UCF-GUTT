"""
UCF/GUTT Extensions Library - Python Implementation
====================================================

A Python implementation of the zero-axiom universal connectivity proofs
from the Coq library. Every relation becomes serial (no dead ends) by
adding a single "Whole" element that everything relates to.

Core Insight:
    The option type (Maybe/Optional) isn't just a data structure—it's a
    theorem about relational completeness. None becomes "the Whole" that
    provides universal connectivity.

License: UCF/GUTT Research & Evaluation License v1.1
Copyright (c) 2023-2025 Michael Fillippini. All Rights Reserved.
"""

from __future__ import annotations
from typing import TypeVar, Generic, Callable, Optional, Iterator, Any, Set, Tuple
from dataclasses import dataclass
from abc import ABC, abstractmethod

__version__ = "1.0.0"
__all__ = [
    "Whole", "Elem", "Carrier", "WholeCompletion",
    "Relation", "LiftedRelation", "SerialExtension",
    "IteratedCompletion", "RelationGraph"
]

T = TypeVar('T')
U = TypeVar('U')

# =============================================================================
#                           CARRIER TYPE
# =============================================================================

class Carrier(ABC, Generic[T]):
    """
    Abstract base for elements in the extended universe U + {Whole}.
    
    Corresponds to Coq's: WholeCompletion.carrier U = option U
    """
    
    @abstractmethod
    def is_whole(self) -> bool:
        """Check if this is the Whole element."""
        pass
    
    @abstractmethod
    def is_elem(self) -> bool:
        """Check if this is an embedded element from U."""
        pass
    
    @abstractmethod
    def get(self) -> Optional[T]:
        """Get the underlying value, or None if Whole."""
        pass
    
    def map(self, f: Callable[[T], U]) -> Carrier[U]:
        """Apply a function to the underlying value (functor map)."""
        if self.is_whole():
            return WholeType()
        return Elem(f(self.get()))
    
    def bind(self, f: Callable[[T], Carrier[U]]) -> Carrier[U]:
        """Monadic bind operation."""
        if self.is_whole():
            return WholeType()
        return f(self.get())


class WholeType(Carrier[Any]):
    """
    The distinguished "Whole" element - universal relational sink.
    
    Corresponds to Coq's: WholeCompletion.point = None
    
    Properties (proven in Coq):
        - Every element relates to Whole (seriality)
        - Whole relates only to itself (terminal)
        - Whole is not in the image of Elem (freshness)
    """
    _instance: Optional[WholeType] = None
    
    def __new__(cls) -> WholeType:
        if cls._instance is None:
            cls._instance = super().__new__(cls)
        return cls._instance
    
    def is_whole(self) -> bool:
        return True
    
    def is_elem(self) -> bool:
        return False
    
    def get(self) -> None:
        return None
    
    def __repr__(self) -> str:
        return "Whole"
    
    def __eq__(self, other: object) -> bool:
        return isinstance(other, WholeType)
    
    def __hash__(self) -> int:
        return hash("Whole")


# Singleton instance
Whole: WholeType = WholeType()


@dataclass(frozen=True)
class Elem(Carrier[T]):
    """
    An embedded element from the base universe U.
    
    Corresponds to Coq's: WholeCompletion.inject u = Some u
    """
    value: T
    
    def is_whole(self) -> bool:
        return False
    
    def is_elem(self) -> bool:
        return True
    
    def get(self) -> T:
        return self.value
    
    def __repr__(self) -> str:
        return f"Elem({self.value!r})"


# =============================================================================
#                           RELATIONS
# =============================================================================

# A relation is a binary predicate
Relation = Callable[[T, T], bool]


class LiftedRelation(Generic[T]):
    """
    A relation lifted to the extended carrier U + {Whole}.
    
    Corresponds to Coq's WholeCompletion.lift_rel with semantics:
        - R'(Elem(a), Elem(b)) = R(a, b)    (conservative)
        - R'(x, Whole) = True               (seriality)  
        - R'(Whole, Elem(_)) = False        (terminal)
        - R'(Whole, Whole) = True           (self-loop)
    """
    
    def __init__(self, base_relation: Relation[T]):
        self._base = base_relation
    
    def __call__(self, x: Carrier[T], y: Carrier[T]) -> bool:
        """Evaluate the lifted relation."""
        # R'(_, Whole) = True (everything relates to Whole)
        if y.is_whole():
            return True
        
        # R'(Whole, Elem(_)) = False (Whole is terminal sink)
        if x.is_whole():
            return False
        
        # R'(Elem(a), Elem(b)) = R(a, b) (conservative)
        return self._base(x.get(), y.get())
    
    @property
    def base(self) -> Relation[T]:
        """Access the underlying base relation."""
        return self._base
    
    def is_serial(self) -> bool:
        """
        Seriality is guaranteed by construction.
        
        Proven in Coq as: WholeCompletion.serial
        """
        return True  # By construction, everything relates to Whole
    
    def successor(self, x: Carrier[T]) -> Carrier[T]:
        """
        Return a guaranteed successor (Whole).
        
        This witnesses the seriality property.
        """
        return Whole


# =============================================================================
#                       WHOLE COMPLETION
# =============================================================================

class WholeCompletion(Generic[T]):
    """
    The canonical serial completion of a universe U.
    
    This is the main entry point. Given any set/type U and relation R,
    produces an extended universe where R becomes serial (no dead ends).
    
    Corresponds to Coq's WholeCompletion module.
    
    Example:
        >>> wc = WholeCompletion()
        >>> lt = wc.lift(lambda a, b: a < b)
        >>> lt(wc.elem(5), wc.elem(10))  # 5 < 10
        True
        >>> lt(wc.elem(100), wc.whole)   # 100 relates to Whole
        True
    """
    
    @property
    def whole(self) -> Carrier[T]:
        """The distinguished Whole element."""
        return Whole
    
    def elem(self, value: T) -> Carrier[T]:
        """Embed a value from U into the extended carrier."""
        return Elem(value)
    
    def lift(self, relation: Relation[T]) -> LiftedRelation[T]:
        """
        Lift a relation to the extended carrier.
        
        The lifted relation is guaranteed to be serial.
        """
        return LiftedRelation(relation)
    
    def is_fresh(self, x: Carrier[T]) -> bool:
        """Check if x is Whole (fresh = not in image of elem)."""
        return x.is_whole()
    
    def carrier_elements(self, base_elements: Iterator[T]) -> Iterator[Carrier[T]]:
        """
        Generate all carrier elements from base elements.
        
        Yields Elem(x) for each x, then Whole.
        """
        for x in base_elements:
            yield Elem(x)
        yield Whole


# =============================================================================
#                       SERIAL EXTENSION
# =============================================================================

class SerialExtension(Generic[T]):
    """
    A complete serial extension with tracked elements.
    
    Extends WholeCompletion with bookkeeping for the base elements,
    useful for graph algorithms and enumeration.
    """
    
    def __init__(self, elements: Optional[Set[T]] = None):
        self._completion = WholeCompletion[T]()
        self._elements: Set[T] = elements or set()
        self._lifted_relations: dict[str, LiftedRelation[T]] = {}
    
    @property
    def whole(self) -> Carrier[T]:
        return self._completion.whole
    
    def add(self, value: T) -> Carrier[T]:
        """Add an element to the universe and return its carrier form."""
        self._elements.add(value)
        return Elem(value)
    
    def elem(self, value: T) -> Carrier[T]:
        """Get carrier form of a value (adds if not present)."""
        self._elements.add(value)
        return Elem(value)
    
    def register_relation(self, name: str, relation: Relation[T]) -> LiftedRelation[T]:
        """Register and lift a named relation."""
        lifted = self._completion.lift(relation)
        self._lifted_relations[name] = lifted
        return lifted
    
    def get_relation(self, name: str) -> Optional[LiftedRelation[T]]:
        """Get a registered relation by name."""
        return self._lifted_relations.get(name)
    
    def all_carriers(self) -> Iterator[Carrier[T]]:
        """Iterate over all carrier elements (elements + Whole)."""
        for x in self._elements:
            yield Elem(x)
        yield Whole
    
    def successors(self, x: Carrier[T], relation_name: str) -> Iterator[Carrier[T]]:
        """Find all successors of x under a named relation."""
        rel = self._lifted_relations.get(relation_name)
        if rel is None:
            return
        
        for y in self.all_carriers():
            if rel(x, y):
                yield y
    
    def has_path(self, start: Carrier[T], end: Carrier[T], relation_name: str, 
                 max_depth: int = 100) -> bool:
        """Check if there's a path from start to end."""
        if start == end:
            return True
        
        rel = self._lifted_relations.get(relation_name)
        if rel is None:
            return False
        
        visited: Set[Carrier[T]] = set()
        frontier = [start]
        
        for _ in range(max_depth):
            if not frontier:
                return False
            
            current = frontier.pop(0)
            if current in visited:
                continue
            visited.add(current)
            
            for succ in self.successors(current, relation_name):
                if succ == end:
                    return True
                if succ not in visited:
                    frontier.append(succ)
        
        return False


# =============================================================================
#                       ITERATED COMPLETION
# =============================================================================

class IteratedCompletion(Generic[T]):
    """
    N-fold Whole-completion for nested relational structures.
    
    Corresponds to Coq's SerialComposition module.
    
    Level 0: U
    Level 1: U + {Whole₀}
    Level 2: U + {Whole₀} + {Whole₁}
    ...
    
    Each level has its own Whole, enabling fractal/hierarchical structures.
    """
    
    def __init__(self, depth: int):
        if depth < 1:
            raise ValueError("Depth must be at least 1")
        self._depth = depth
    
    @property
    def depth(self) -> int:
        return self._depth
    
    def inject(self, value: T) -> Carrier:
        """Inject a value at the deepest level."""
        result: Carrier = Elem(value)
        for _ in range(self._depth):
            result = Elem(result)
        return result
    
    def whole_at_level(self, level: int) -> Carrier:
        """
        Get the Whole at a specific level.
        
        Level 0 = outermost, Level (depth-1) = innermost
        """
        if level < 0 or level >= self._depth:
            raise ValueError(f"Level must be 0 to {self._depth - 1}")
        
        # Build from inside out
        result: Carrier = Whole
        for _ in range(self._depth - level - 1):
            result = Elem(result)
        return result
    
    def all_wholes(self) -> Iterator[Carrier]:
        """Iterate over all Whole elements at all levels."""
        for level in range(self._depth):
            yield self.whole_at_level(level)


# =============================================================================
#                       RELATION GRAPH
# =============================================================================

class RelationGraph(Generic[T]):
    """
    Graph representation of a relation over a serial extension.
    
    Useful for visualization and graph algorithms.
    """
    
    def __init__(self, extension: SerialExtension[T], relation_name: str):
        self._ext = extension
        self._rel_name = relation_name
    
    def edges(self) -> Iterator[Tuple[Carrier[T], Carrier[T]]]:
        """Generate all edges (x, y) where R(x, y) holds."""
        rel = self._ext.get_relation(self._rel_name)
        if rel is None:
            return
        
        carriers = list(self._ext.all_carriers())
        for x in carriers:
            for y in carriers:
                if rel(x, y):
                    yield (x, y)
    
    def to_dict(self) -> dict[str, list[str]]:
        """Convert to adjacency list representation."""
        result: dict[str, list[str]] = {}
        for x, y in self.edges():
            key = str(x)
            if key not in result:
                result[key] = []
            result[key].append(str(y))
        return result
    
    def edge_count(self) -> int:
        """Count total edges."""
        return sum(1 for _ in self.edges())
    
    def verify_seriality(self) -> bool:
        """
        Verify that every element has at least one successor.
        
        This should always return True by construction.
        """
        rel = self._ext.get_relation(self._rel_name)
        if rel is None:
            return False
        
        for x in self._ext.all_carriers():
            has_successor = any(rel(x, y) for y in self._ext.all_carriers())
            if not has_successor:
                return False
        return True


# =============================================================================
#                       CONVENIENCE FUNCTIONS
# =============================================================================

def complete(elements: Set[T], relation: Relation[T]) -> SerialExtension[T]:
    """
    Quick way to create a serial extension from elements and a relation.
    
    Example:
        >>> ext = complete({1, 2, 3}, lambda a, b: a < b)
        >>> lt = ext.get_relation("R")
        >>> lt(ext.elem(1), ext.whole)
        True
    """
    ext = SerialExtension(elements)
    ext.register_relation("R", relation)
    return ext


def lift(relation: Relation[T]) -> LiftedRelation[T]:
    """
    Lift a relation to include Whole.
    
    Example:
        >>> lt = lift(lambda a, b: a < b)
        >>> lt(Elem(5), Whole)
        True
    """
    return WholeCompletion[T]().lift(relation)
