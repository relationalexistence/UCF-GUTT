# UCF/GUTT Math Demos — Numbers & Irrationals

`Ucf_math_demos.py` — three hands-on Python demonstrations that mirror
verified Coq theorems from the UCF/GUTT public core. Exact-rational
arithmetic, Python standard library only, runs as a CLI or imports
cleanly into a notebook or larger pipeline.

For a demo-first tour with output included, see [Public Math Core](https://relationalexistence.com/public-math-core). For the API and the Q-vs-R reasoning, read on.

This module is a *companion* to the Coq library, not a substitute for it.
The proofs live in Coq. The Python lets a reader see what the formal
theorems are asserting, on concrete inputs, with the same constructive
arithmetic semantics the Coq files commit to (`Q` via `Coq.QArith`,
mirrored here by `fractions.Fraction`).

---

## What it covers

| Demo | Coq source file                            | What you see                                                                |
|------|--------------------------------------------|-----------------------------------------------------------------------------|
| 1    | `Top__Numbers__RelationalIrrationals.v`    | Parity descent on candidate p/q; Newton iteration in Q with exact deficit  |
| 2    | `Top__Numbers__Relational.v` + `RelationalIntegers.v` | Iterated Euclid step; smallest-prime-factor extraction; fresh-prime witness |
| 3    | `Top__Numbers__RelationalDivision.v`       | 1/0 routed through three relational contexts; full truth table              |

The Coq files referenced above each close under `Print Assumptions` as
"Closed under the global context" — zero axioms, zero admits, no
classical logic, no functional extensionality, no propositional
extensionality.

---

## Arithmetic policy

Every numeric value that feeds a demonstration claim is an exact
`fractions.Fraction` or an integer. `float` never appears in any
computation whose result is asserted. The single exception is a
display-only `float(|deficit|)` rendering in the Newton table, used to
give the reader an order-of-magnitude feel; the exact rational beside it
is the actual datum.

This mirrors the Coq library's decision to live in `Coq.QArith` (Q)
rather than `Coq.Reals` (R). Q is constructive and decidable; R drags in
`ClassicalDedekindReals` and dependent classical machinery. Staying in
Q on both sides means a Python computation here can be re-played as a
`Compute` in Coq and the bits will match.

---

## Demo 1 — √2 ∉ ℚ

Two parts.

**Parity descent** (`sqrt2_descent_witness(p, q)`). Given a candidate
p/q, reduce to lowest terms (p', q') = (p/g, q/g) where g = gcd(p, q),
then exhibit (p')² and 2(q')² as exact integers. The two are never
equal in lowest terms; the witness records the gap directly. When the
equation does hold (it never does for coprime p', q'), the witness also
records the parities, which would force 2 | gcd(p', q') and contradict
gcd(p', q') = 1.

**Newton iteration in Q** (`cauchy_sqrt2(n)`). The Babylonian / Newton
recurrence x_{n+1} = (x_n + 2/x_n) / 2, applied entirely in Q starting
from x_0 = 1. Each step returns a `NewtonStep` with the exact x_n, the
exact x_n², and the exact deficit (x_n² − 2).

Sample trace, first nine terms:

```
n  x_n (exact)             x_n² − 2 (exact)         |deficit| (float)
0  1/1                     -1/1                     1.000e+00
1  3/2                      1/4                     2.500e-01
2  17/12                    1/144                   6.944e-03
3  577/408                  1/166464                6.007e-06
4  665857/470832            1/221682772224          4.511e-12
5  886731088897/...          1/393146012008...      2.544e-24
6  1572584048032918633.../  1/12365102940638...     8.087e-49
7  4946041176255201878.../  1/12231661658605...     8.176e-98
8  4892664663442388195.../  1/11969083754448...     8.355e-196
```

The denominator-cascade is quadratic convergence visible in exact
integers: deficit_{n+1} ≈ deficit_n² / 8, which is the theoretical
Newton-Raphson rate for f(x) = x² − 2. Every x_n is rational, every
deficit is a nonzero rational, and the limit is provably not in Q. The
sequence *is* the constructive R_cauchy story for √2.

Corresponding Coq content:
- The Babylonian recurrence is defined as `babylon_step` and iterated
  as `sqrt2_seq` in `Top__Numbers__RelationalIrrationals.v`.
- The sequence is proven Cauchy: `sqrt2_cauchy_mod`.
- The sequence is proven to satisfy `(sqrt2_seq n)² → 2`:
  `sqrt2_sq_converges_to_2`.
- The headline irrationality theorem is `sqrt2_not_rational_Z`
  (`forall p q : Z, q ≠ 0 → ¬ (p² = 2 q²)`), with an equivalent
  formulation as `no_rational_squares_to_2`.

---

## Demo 2 — infinitude of primes (Euclid in N_rel)

`euclid_step(primes)` takes a finite list of primes [p₁, …, p_k] and
returns an `EuclidStep` record containing the input list, N =
p₁·…·p_k + 1, the smallest prime factor of N, and a flag confirming the
new prime is not in the input (always True by the divisibility
argument: any p_i divides product, so it cannot divide product+1).

`euclid_chain(seed, steps)` iterates the construction, accumulating
new primes into the working list.

Sample chain from seed {2}:

```
step  input primes            N = prod+1   new prime
   1  2                       3            3
   2  2, 3                    7            7
   3  2, 3, 7                 43           43
   4  2, 3, 7, 43             1807         13      ← 1807 = 13·139
   5  2, 3, 7, 43, 13         23479        53
   6  2, 3, 7, 43, 13, 53     1244335      5       ← 1244335 = 5·…
```

This is denser than Sylvester's sequence: small primes can be pulled in
late if the seed missed them (5 lands at step 6 here, even though it is
the third-smallest prime). The "smallest prime factor of product+1"
rule is what causes this — Sylvester's sequence would keep taking
product+1 itself.

Corresponding Coq content lives in
`Top__Numbers__RelationalIntegers.v` (divisibility, gcd, lcm over Z_rel)
and `Top__Numbers__Relational.v` (the N_rel structure). The "no maximal
prime" statement is a counting argument over those.

---

## Demo 3 — totalized division (three relational contexts)

The Coq file `Top__Numbers__RelationalDivision.v` makes Q-division total
by routing 1/0 through a `RelCtx`. The three context-specific routings
are separate theorems:

| Coq theorem               | Context     | Output for b = 0        |
|---------------------------|-------------|-------------------------|
| `Q_contextual_space_infty` | `RC_Space` | `PinftyQ` (+∞)          |
| `Q_contextual_time_zero`   | `RC_Time`  | `FiniteQ 0`             |
| `Q_contextual_info_nan`    | `RC_Info`  | `ExtNaNQ`               |

For b ≠ 0, all three contexts agree on `FiniteQ (a/b)` (the
`Q_contextual_div_conservative` theorem). Boundary detection
(`Q_boundary_detect`) lives at a layer below routing — it depends only
on b == 0, not on context, which is exactly what `Q_boundary_iff_zero`
encodes.

Sample truth table:

```
context     a       b       a / b              boundary?
RC_Space    5/1     0/1     PinftyQ            RS_Boundary
RC_Space    1/1     0/1     PinftyQ            RS_Boundary
RC_Space    6/1     2/1     FiniteQ(3/1)       RS_Related
RC_Time     5/1     0/1     FiniteQ(0/1)       RS_Boundary
RC_Time     1/1     0/1     FiniteQ(0/1)       RS_Boundary
RC_Time     6/1     2/1     FiniteQ(3/1)       RS_Related
RC_Info     5/1     0/1     ExtNaNQ            RS_Boundary
RC_Info     1/1     0/1     ExtNaNQ            RS_Boundary
RC_Info     6/1     2/1     FiniteQ(3/1)       RS_Related
```

No partiality: every cell is a fully-defined `ExtendedQ`.

---

## Running

```
python3 ucf_math_demos.py                  # all three demos
python3 ucf_math_demos.py sqrt2 12         # 12 Newton steps
python3 ucf_math_demos.py primes 10        # 10 Euclid steps
python3 ucf_math_demos.py div              # totalized-division truth table
python3 ucf_math_demos.py --help
```

Python 3.8+. Standard library only — `fractions`, `dataclasses`,
`enum`, `math`, `sys`, `typing`. No installation, no third-party
dependencies, nothing to pin.

---

## As a library

Every demo function returns structured data, not just printed text, so
the module can drive a notebook, a Streamlit page, or a downstream
certifier without modification.

```python
import ucf_math_demos as m
from fractions import Fraction

# Demo 1: Newton trace as a list of NewtonStep records
trace = m.cauchy_sqrt2(8)
trace[8].x            # Fraction, full numerator/denominator visible
trace[8].x_squared    # Fraction (x² in exact form)
trace[8].deficit      # Fraction, sign tracked, never zero

# Demo 1: descent witness on a candidate p/q
w = m.sqrt2_descent_witness(577, 408)
w.p_squared, w.two_q_squared      # (332929, 332928)
w.holds_equation                   # False

# Demo 2: a single Euclid step
step = m.euclid_step([2, 3, 5])
step.product_plus_one   # 31
step.new_prime          # 31
step.new_prime_is_new   # True

# Demo 3: contextual division
m.Q_contextual_div(
    m.RelationalContext.SPACE,
    Fraction(1),
    Fraction(0),
)
# ExtendedQ(kind='+inf', value=None)

m.Q_boundary_detect(Fraction(0))   # RelationalState.BOUNDARY
m.Q_boundary_detect(Fraction(1,3)) # RelationalState.RELATED
```

---

## Coq correspondence

| Python symbol                 | Coq symbol                                                       |
|-------------------------------|------------------------------------------------------------------|
| `sqrt2_descent_witness`       | `sqrt2_not_rational_Z`, `no_rational_squares_to_2`              |
| `cauchy_sqrt2` / `NewtonStep` | `sqrt2_seq` + `babylon_step` + `sqrt2_cauchy_mod` + `sqrt2_sq_converges_to_2` |
| `smallest_prime_factor`       | divisibility / gcd lemmas in `Top__Numbers__RelationalIntegers.v` |
| `euclid_step` / `EuclidStep`  | counting argument over N_rel (`Top__Numbers__Relational.v`)      |
| `RelationalContext`           | `RelCtx` (`RC_Space \| RC_Time \| RC_Info`)                      |
| `RelationalState`             | `RelationalState` (`RS_Related \| RS_Boundary \| RS_Undefined`)  |
| `ExtendedQ`                   | `ExtQ` (`FiniteQ \| PinftyQ \| MinftyQ \| ExtNaNQ`)              |
| `Q_boundary_detect`           | `Q_boundary_detect` + `Q_boundary_iff_zero`                      |
| `Q_contextual_div`            | `Q_contextual_div` + `Q_contextual_space_infty` / `Q_contextual_time_zero` / `Q_contextual_info_nan` |

### Vocabulary differences worth knowing

The Python uses slightly longer identifiers than the Coq for
readability at the call site:

- `RelationalContext` (Python) ↔ `RelCtx` (Coq); the three constructors
  `RC_Space / RC_Time / RC_Info` are identical on both sides.
- `ExtendedQ` (Python) ↔ `ExtQ` (Coq). The Coq inductive has four
  constructors (`FiniteQ`, `PinftyQ`, `MinftyQ`, `ExtNaNQ`); the
  Python keeps only the three reachable from `Q_contextual_div` on
  b = 0. `MinftyQ` exists in the Coq for symmetry under negation but
  is not the target of any contextual-division theorem, so the Python
  is faithful to the routings as actually proven.

---

## Interpretation of scope

This module demonstrates the *behaviour* of specific Coq theorems on
specific inputs. It does not extend, generalize, reinterpret, or
prove anything about those theorems. Claims about UCF/GUTT as a
framework — relational ontology, Whole-completion, seriality,
tensor invariants, the wider proposition catalogue — are not made or
supported by this file.

For the formal substrate, see the public Coq core
(`https://github.com/relationalexistence/UCF-GUTT`). For framework
background, see <https://relationalexistence.com>.

---

## License

Apache-2.0. © 2023–2026 Michael Fillippini.

The names **UCF/GUTT**, **GUTT-L**, **LANTOSE**, **NRTML**, **RCTT**, and
**Relational Existence** are trademarks of Michael Fillippini; the
Apache 2.0 license grants no rights in these trademarks.

If you reference this companion module in academic work, please cite
the underlying Coq library:

> Fillippini, M. (2026). *UCF/GUTT Coq Library — Public Core, v2.0.0.*
> Zero-axiom Coq formalization of relational ontology.
