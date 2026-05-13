#!/usr/bin/env python3
# =============================================================================
#   UCF/GUTT(TM) -- Mathematical Demonstrations: Numbers & Irrationals
#   Copyright 2023-2026 Michael Fillippini.
#
#   Licensed under the Apache License, Version 2.0 (the "License").
#       http://www.apache.org/licenses/LICENSE-2.0
#
#   SPDX-License-Identifier: Apache-2.0
# =============================================================================
"""
UCF/GUTT Numbers & Irrationals -- hands-on demonstrations.

A Python companion to the public Coq core, mirroring the verified content of:

    Top__Numbers__Relational           (N_rel)
    Top__Numbers__RelationalIntegers   (Z_rel)
    Top__Numbers__RelationalRationals  (Q_rel)
    Top__Numbers__RelationalReals      (R_cauchy)
    Top__Numbers__RelationalIrrationals (sqrt 2 not in Q)
    Top__Numbers__RelationalDivision   (totalized division, 3 contexts)

ARITHMETIC POLICY
-----------------
All numeric values are exact rationals (`fractions.Fraction`) or integers.
No `float` ever appears in a computation that feeds a demonstration claim.
This mirrors the Coq library's Q-based, zero-classical-axiom discipline:
every numerical witness exhibited here can be re-derived bit-for-bit by a
Coq script over `Coq.QArith`, which is exactly where the formal proofs live.

THREE DEMOS
-----------
DEMO 1 -- sqrt(2) is not in Q.
    (a) Constructive parity descent: any p/q in lowest terms with p^2 = 2q^2
        produces an explicit pair (p, q) both even, contradicting gcd(p,q)=1.
    (b) Newton iteration in Q producing a Cauchy sequence (x_n) of rationals
        with x_n^2 -> 2 but x_n^2 != 2 for every n. The sequence lives entirely
        inside Q; its limit demonstrably does not.

DEMO 2 -- infinitude of primes (Euclid's construction in N_rel).
    Given any finite list of primes [p_1, ..., p_k], compute
    N = p_1 * ... * p_k + 1 and exhibit the smallest prime factor of N
    as a prime not in the input list. Iterating this gives a strictly
    increasing chain of primes from any seed.

DEMO 3 -- totalized division (three relational contexts).
    The Coq library `Top__Numbers__RelationalDivision` totalizes a/0 by
    routing through a `RelationalContext`:
        RC_Space -> PinftyQ      (1/0 = +infinity)
        RC_Time  -> FiniteQ 0    (1/0 = 0)
        RC_Info  -> ExtNaNQ      (1/0 = NaN)
    Each routing is a separate Coq theorem
    (`Q_contextual_space_infty`, `Q_contextual_time_zero`,
    `Q_contextual_info_nan`). This module implements the same three
    routings with the same semantics.

USAGE
-----
    python3 ucf_math_demos.py               # runs all three demos
    python3 ucf_math_demos.py sqrt2 12      # 12 Newton steps toward sqrt(2)
    python3 ucf_math_demos.py primes 10     # 10 Euclidean steps
    python3 ucf_math_demos.py div           # totalized-division truth table

The module is also importable: every demo function returns structured data,
not just printed text, so it can drive a notebook, a Streamlit page, or a
downstream certifier.
"""

from __future__ import annotations

import math
import sys
from dataclasses import dataclass, field
from enum import Enum
from fractions import Fraction
from typing import Iterator, List, Optional, Sequence, Tuple


# =============================================================================
#   SECTION 1: SHARED HELPERS
# =============================================================================

def _hr(width: int = 72, char: str = "=") -> str:
    return char * width


def _banner(title: str, width: int = 72) -> str:
    return f"{_hr(width)}\n  {title}\n{_hr(width)}"


# =============================================================================
#   SECTION 2: DEMO 1 -- sqrt(2) is not in Q
#
#   Coq reference: Top__Numbers__RelationalIrrationals.v
# =============================================================================

@dataclass(frozen=True)
class DescentWitness:
    """A finite, fully-displayable witness that p^2 != 2q^2 in lowest terms.

    The witness encodes the classical parity descent:
      Suppose p/q is in lowest terms (gcd(p,q) = 1) and p^2 = 2q^2. Then
      p^2 is even, so p is even, so p = 2k for some k, so 4k^2 = 2q^2, so
      q^2 = 2k^2, so q is even. But then 2 | gcd(p,q), contradicting
      gcd(p,q) = 1. This single chain of parity checks is the witness.
    """
    p_input: int
    q_input: int
    g: int                    # gcd(p, q)
    p_reduced: int            # p // g
    q_reduced: int            # q // g
    p_squared: int            # p_reduced ** 2
    two_q_squared: int        # 2 * q_reduced ** 2
    holds_equation: bool      # p_squared == two_q_squared
    p_is_even: Optional[bool] # only set if holds_equation
    q_is_even: Optional[bool] # only set if holds_equation

    def as_lines(self) -> List[str]:
        out = [
            f"  input         : p = {self.p_input}, q = {self.q_input}",
            f"  gcd(p,q)      : {self.g}",
            f"  reduced form  : p' = {self.p_reduced}, q' = {self.q_reduced}",
            f"  (p')^2        : {self.p_squared}",
            f"  2 * (q')^2    : {self.two_q_squared}",
            f"  equation holds: {self.holds_equation}",
        ]
        if self.holds_equation:
            out += [
                f"  p' even?      : {self.p_is_even}",
                f"  q' even?      : {self.q_is_even}",
                "  -> both even contradicts gcd(p',q') = 1",
            ]
        else:
            out += ["  -> (p')^2 != 2*(q')^2 by direct integer arithmetic"]
        return out


def sqrt2_descent_witness(p: int, q: int) -> DescentWitness:
    """Build a finite witness that p/q cannot satisfy (p/q)^2 = 2.

    For any (p, q) with q != 0 this terminates with a contradiction.
    Mirrors the Coq theorem
        sqrt_2_irrational : forall p q : nat, q <> 0 ->
                            gcd p q = 1 -> p*p <> 2 * (q*q).
    """
    if q == 0:
        raise ValueError("q must be nonzero")
    g = math.gcd(abs(p), abs(q))
    p_r = p // g if g else p
    q_r = q // g if g else q
    p_sq = p_r * p_r
    two_q_sq = 2 * q_r * q_r
    holds = (p_sq == two_q_sq)
    return DescentWitness(
        p_input=p,
        q_input=q,
        g=g,
        p_reduced=p_r,
        q_reduced=q_r,
        p_squared=p_sq,
        two_q_squared=two_q_sq,
        holds_equation=holds,
        p_is_even=(p_r % 2 == 0) if holds else None,
        q_is_even=(q_r % 2 == 0) if holds else None,
    )


@dataclass(frozen=True)
class NewtonStep:
    n: int
    x: Fraction
    x_squared: Fraction
    deficit: Fraction         # x^2 - 2 (exact rational, sign tracked)

    @property
    def deficit_abs(self) -> Fraction:
        return -self.deficit if self.deficit < 0 else self.deficit


def cauchy_sqrt2(n_terms: int, x0: Fraction = Fraction(1)) -> List[NewtonStep]:
    """Newton iteration in Q: x_{n+1} = (x_n + 2/x_n) / 2.

    Returns a list of `NewtonStep` records, each one entirely in Q.
    Every step satisfies x_n^2 != 2 (exactly, in Q), but the deficit
    |x_n^2 - 2| descends to zero. This is the canonical demonstration
    that the limit of the sequence (which is sqrt(2)) is not in Q.

    Mirrors the constructive R_cauchy approach in
        Top__Numbers__RelationalReals.v
    where reals are equivalence classes of rational Cauchy sequences.
    """
    if n_terms < 0:
        raise ValueError("n_terms must be >= 0")
    if x0 <= 0:
        raise ValueError("starting point must be > 0")
    two = Fraction(2)
    x = x0
    steps = [NewtonStep(n=0, x=x, x_squared=x * x, deficit=x * x - two)]
    for n in range(1, n_terms + 1):
        x = (x + two / x) / 2
        x_sq = x * x
        steps.append(NewtonStep(n=n, x=x, x_squared=x_sq, deficit=x_sq - two))
    return steps


def demo_sqrt2(newton_terms: int = 8) -> dict:
    """Run the sqrt(2)-not-in-Q demonstration end to end.

    Returns a dict containing both the descent witness and the Newton trace,
    so callers (CLI, notebook, Streamlit) can re-render however they like.
    """
    # Part (a): a few candidate fractions p/q each fail the parity check.
    candidates: List[Tuple[int, int]] = [(3, 2), (7, 5), (17, 12), (577, 408)]
    descents = [sqrt2_descent_witness(p, q) for p, q in candidates]

    # Part (b): Newton trace.
    newton = cauchy_sqrt2(newton_terms)

    return {"descents": descents, "newton": newton}


def _print_sqrt2_demo(result: dict) -> None:
    print(_banner("DEMO 1 -- sqrt(2) is not in Q"))
    print(
        "Coq reference: Top__Numbers__RelationalIrrationals.v\n"
        "Theorem: forall p q : nat, q <> 0 -> gcd p q = 1 -> p*p <> 2 * (q*q)\n"
    )
    print("(a) Parity descent on candidate p/q values:\n")
    for w in result["descents"]:
        for line in w.as_lines():
            print(line)
        print()

    print("(b) Newton iteration x_{n+1} = (x_n + 2/x_n) / 2, entirely in Q:\n")
    print(f"  {'n':>3}  {'x_n (exact)':<22}  {'x_n^2 - 2 (exact)':<28}  "
          f"{'|deficit| as float':<22}")
    print(f"  {'-'*3}  {'-'*22}  {'-'*28}  {'-'*22}")
    for s in result["newton"]:
        x_str = f"{s.x.numerator}/{s.x.denominator}"
        d_str = f"{s.deficit.numerator}/{s.deficit.denominator}"
        # Only used for display, not for any claim:
        d_disp = float(s.deficit_abs)
        print(f"  {s.n:>3}  {x_str:<22}  {d_str:<28}  {d_disp:.3e}")
    print(
        "\n  Every x_n is rational. Every deficit (x_n^2 - 2) is a nonzero\n"
        "  rational. The limit -- sqrt(2) -- is NOT in Q. The sequence is\n"
        "  the canonical Cauchy witness for the irrational it represents.\n"
    )


# =============================================================================
#   SECTION 3: DEMO 2 -- infinitude of primes (Euclid in N_rel)
#
#   Coq reference: Top__Numbers__Relational.v (N_rel)
#                  Top__Numbers__RelationalIntegers.v (Z_rel, divisibility)
# =============================================================================

def _is_prime(n: int) -> bool:
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    r = math.isqrt(n)
    for d in range(3, r + 1, 2):
        if n % d == 0:
            return False
    return True


def smallest_prime_factor(n: int) -> int:
    """Return the smallest prime factor of n >= 2.

    Total, terminating, integer-only -- no rationals or reals needed.
    """
    if n < 2:
        raise ValueError("n must be >= 2")
    if n % 2 == 0:
        return 2
    r = math.isqrt(n)
    d = 3
    while d <= r:
        if n % d == 0:
            return d
        d += 2
    return n  # n itself is prime


@dataclass(frozen=True)
class EuclidStep:
    input_primes: Tuple[int, ...]   # immutable copy
    product_plus_one: int           # p_1 * ... * p_k + 1
    new_prime: int                  # smallest prime factor of product_plus_one
    new_prime_is_new: bool          # always True by construction


def euclid_step(primes: Sequence[int]) -> EuclidStep:
    """Given a finite list of primes, exhibit a prime not in the list.

    The construction:
        N = (product of input primes) + 1
        q = smallest prime factor of N
    Then q does not divide any of the input primes (since p_i divides
    N - 1 but not N), so q is a fresh prime.
    """
    for p in primes:
        if not _is_prime(p):
            raise ValueError(f"input contains non-prime: {p}")
    product = 1
    for p in primes:
        product *= p
    n = product + 1
    q = smallest_prime_factor(n)
    return EuclidStep(
        input_primes=tuple(primes),
        product_plus_one=n,
        new_prime=q,
        new_prime_is_new=(q not in primes),
    )


def euclid_chain(seed: Sequence[int], steps: int) -> List[EuclidStep]:
    """Run Euclid's construction `steps` times, accumulating new primes."""
    if steps < 0:
        raise ValueError("steps must be >= 0")
    primes = list(seed)
    trace: List[EuclidStep] = []
    for _ in range(steps):
        st = euclid_step(primes)
        trace.append(st)
        primes.append(st.new_prime)
    return trace


def demo_primes(steps: int = 6) -> dict:
    trace = euclid_chain(seed=[2], steps=steps)
    return {"trace": trace}


def _print_primes_demo(result: dict) -> None:
    print(_banner("DEMO 2 -- infinitude of primes (Euclid in N_rel)"))
    print(
        "Coq reference: counting argument over N_rel\n"
        "  Top__Numbers__Relational.v  (N_rel structure)\n"
        "  Top__Numbers__RelationalIntegers.v  (divisibility)\n"
    )
    print("Iterating Euclid: at each step, take the product of all known\n"
          "primes plus 1, then extract its smallest prime factor.\n")
    print(f"  {'step':>4}  {'input primes':<30}  {'N = prod+1':<20}  "
          f"{'new prime'}")
    print(f"  {'-'*4}  {'-'*30}  {'-'*20}  {'-'*9}")
    for i, st in enumerate(result["trace"], start=1):
        in_str = ", ".join(str(p) for p in st.input_primes)
        if len(in_str) > 28:
            in_str = in_str[:25] + "..."
        n_str = str(st.product_plus_one)
        if len(n_str) > 18:
            n_str = n_str[:15] + "..."
        print(f"  {i:>4}  {in_str:<30}  {n_str:<20}  {st.new_prime}")
    print(
        "\n  Each new prime is provably not in the input list (it divides\n"
        "  product+1 but no input prime does). The chain is unbounded by\n"
        "  construction -- N_rel has no maximal prime.\n"
    )


# =============================================================================
#   SECTION 4: DEMO 3 -- totalized division (three relational contexts)
#
#   Coq reference: Top__Numbers__RelationalDivision.v
# =============================================================================

class RelationalContext(Enum):
    """Mirrors Coq `RelationalContext` (RC_Space | RC_Time | RC_Info)."""
    SPACE = "RC_Space"
    TIME = "RC_Time"
    INFO = "RC_Info"


class RelationalState(Enum):
    """Mirrors Coq `RelationalState` (RS_Related | RS_Boundary | RS_Undefined)."""
    RELATED = "RS_Related"
    BOUNDARY = "RS_Boundary"
    UNDEFINED = "RS_Undefined"


@dataclass(frozen=True)
class ExtendedQ:
    """Mirrors Coq `ExtendedQ` (FiniteQ q | PinftyQ | ExtNaNQ)."""
    kind: str  # one of: "finite", "+inf", "NaN"
    value: Optional[Fraction] = None

    def __post_init__(self) -> None:
        if self.kind not in ("finite", "+inf", "NaN"):
            raise ValueError(f"bad ExtendedQ kind: {self.kind}")
        if self.kind == "finite" and self.value is None:
            raise ValueError("FiniteQ requires a value")
        if self.kind != "finite" and self.value is not None:
            raise ValueError(f"{self.kind} cannot carry a value")

    def __str__(self) -> str:
        if self.kind == "finite":
            v = self.value
            return f"FiniteQ({v.numerator}/{v.denominator})"
        if self.kind == "+inf":
            return "PinftyQ"
        return "ExtNaNQ"

    @classmethod
    def finite(cls, q: Fraction) -> "ExtendedQ":
        return cls(kind="finite", value=q)

    @classmethod
    def pinfty(cls) -> "ExtendedQ":
        return cls(kind="+inf")

    @classmethod
    def nan(cls) -> "ExtendedQ":
        return cls(kind="NaN")


def Q_boundary_detect(q: Fraction) -> RelationalState:
    """Mirrors Coq `Q_boundary_detect`.

    Returns RS_Boundary iff q == 0, otherwise RS_Related. This is decidable
    in Q -- no classical content is invoked.
    """
    return RelationalState.BOUNDARY if q == 0 else RelationalState.RELATED


def Q_contextual_div(ctx: RelationalContext,
                     a: Fraction,
                     b: Fraction) -> ExtendedQ:
    """Mirrors Coq `Q_contextual_div`.

    The three Coq theorems:
        Q_contextual_space_infty : ctx=RC_Space, b==0 -> PinftyQ
        Q_contextual_time_zero   : ctx=RC_Time,  b==0 -> FiniteQ 0
        Q_contextual_info_nan    : ctx=RC_Info,  b==0 -> ExtNaNQ
    For b != 0, all three contexts agree on FiniteQ(a/b).
    """
    if b == 0:
        if ctx is RelationalContext.SPACE:
            return ExtendedQ.pinfty()
        if ctx is RelationalContext.TIME:
            return ExtendedQ.finite(Fraction(0))
        return ExtendedQ.nan()
    return ExtendedQ.finite(a / b)


def demo_div() -> dict:
    """Build the totalized-division truth table for representative inputs."""
    table: List[Tuple[RelationalContext, Fraction, Fraction, ExtendedQ]] = []
    inputs: List[Tuple[Fraction, Fraction]] = [
        (Fraction(5), Fraction(0)),     # boundary
        (Fraction(0), Fraction(0)),     # boundary, numerator also zero
        (Fraction(1), Fraction(0)),     # the canonical 1/0
        (Fraction(6), Fraction(2)),     # ordinary 6/2 = 3
        (Fraction(1, 3), Fraction(2)),  # ordinary (1/3) / 2 = 1/6
    ]
    for ctx in RelationalContext:
        for a, b in inputs:
            table.append((ctx, a, b, Q_contextual_div(ctx, a, b)))
    return {"table": table}


def _print_div_demo(result: dict) -> None:
    print(_banner("DEMO 3 -- totalized division (three relational contexts)"))
    print(
        "Coq reference: Top__Numbers__RelationalDivision.v\n"
        "Total Q division where 1/0 is not an error but a boundary routed\n"
        "by relational context:\n"
        "    RC_Space -> PinftyQ      (1/0 = +infinity)\n"
        "    RC_Time  -> FiniteQ 0    (1/0 = 0)\n"
        "    RC_Info  -> ExtNaNQ      (1/0 = NaN)\n"
    )
    print(f"  {'context':<10}  {'a':<10}  {'b':<10}  {'a / b':<22}  "
          f"{'boundary?'}")
    print(f"  {'-'*10}  {'-'*10}  {'-'*10}  {'-'*22}  {'-'*9}")
    for ctx, a, b, out in result["table"]:
        a_str = f"{a.numerator}/{a.denominator}"
        b_str = f"{b.numerator}/{b.denominator}"
        bdy = Q_boundary_detect(b).value
        print(f"  {ctx.value:<10}  {a_str:<10}  {b_str:<10}  "
              f"{str(out):<22}  {bdy}")
    print(
        "\n  No partiality: every cell returns a fully-defined ExtendedQ.\n"
        "  The three context-specific theorems above are reflected exactly\n"
        "  in the three rows where b = 0.\n"
    )


# =============================================================================
#   SECTION 5: CLI
# =============================================================================

def _print_header() -> None:
    print(_banner("UCF/GUTT Mathematical Demonstrations -- Numbers & Irrationals",
                  width=72))
    print(
        "Hands-on Python companion to the public Coq core.\n"
        "All arithmetic is exact (fractions.Fraction); no float ever feeds\n"
        "a claim. Demonstrations correspond bit-for-bit to theorems in:\n"
        "  Top__Numbers__Relational           (N_rel)\n"
        "  Top__Numbers__RelationalIntegers   (Z_rel)\n"
        "  Top__Numbers__RelationalRationals  (Q_rel)\n"
        "  Top__Numbers__RelationalReals      (R_cauchy)\n"
        "  Top__Numbers__RelationalIrrationals\n"
        "  Top__Numbers__RelationalDivision\n"
    )


def main(argv: Optional[List[str]] = None) -> int:
    argv = list(sys.argv[1:] if argv is None else argv)

    _print_header()

    if not argv:
        _print_sqrt2_demo(demo_sqrt2(newton_terms=8))
        _print_primes_demo(demo_primes(steps=6))
        _print_div_demo(demo_div())
        return 0

    cmd = argv[0].lower()
    if cmd in ("sqrt2", "irrational", "irr"):
        n = int(argv[1]) if len(argv) > 1 else 8
        _print_sqrt2_demo(demo_sqrt2(newton_terms=n))
        return 0
    if cmd in ("primes", "euclid"):
        n = int(argv[1]) if len(argv) > 1 else 6
        _print_primes_demo(demo_primes(steps=n))
        return 0
    if cmd in ("div", "division", "totalized"):
        _print_div_demo(demo_div())
        return 0
    if cmd in ("-h", "--help", "help"):
        print(__doc__)
        return 0

    print(f"unknown command: {cmd}", file=sys.stderr)
    print("try: sqrt2 [N] | primes [N] | div | help", file=sys.stderr)
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
