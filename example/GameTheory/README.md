# UCF/GUTT GameTheory — Public Release

**Strategic specification → formal certification →
machine-checked causal-security guarantee.**

This release contains two artifacts:

| File | What it is |
|---|---|
| `WHITEPAPER_GAMETHEORY.pdf` | Why this matters: the problem, the certified class, a worked example, the architecture, three structural compression results, scope and limitations. Read this first. |
| `ucfgutt_gametheory_demo.py` | An interactive demonstrator of the certification decision surface. Run this second. |

The underlying theorem library (Coq 8.18, zero axioms —
`coqchk` reports `Axioms: <none>` over the full proof closure)
and the certifying compiler are private; this release shows
what the system **decides** and what acceptance **means**.

## Requirements

Python 3.8+ — standard library only. No installation.

## Quick start

    python3 ucfgutt_gametheory_demo.py --all

runs all six frozen examples. They deliberately span the three
possible outcomes:

- **ACCEPTED** — at punishment windows T = 2, 3, 4, and 6. Each
  of these four configurations is backed by a real generated
  Coq certificate (`KERNEL WITNESS: VERIFIED`).
- **INADMISSIBLE** — a mechanism whose punishment pays better
  than cooperation is refused at the static contract, with the
  failing obligation named.
- **ADMISSIBLE BUT REFUSED** — a sound mechanism at a discount
  factor too low for deterrence: the certificate fails at that
  point, with the exact failing inequality shown.

## Commands

    python3 ucfgutt_gametheory_demo.py --list           # name the examples
    python3 ucfgutt_gametheory_demo.py --example alt-T3 # run one example
    python3 ucfgutt_gametheory_demo.py --spec my.json   # run YOUR spec
    python3 ucfgutt_gametheory_demo.py --all            # run everything

## Writing your own specification

All values are **exact rationals written as strings** ("7/2",
"1/2", "2"). `T` is the punishment window (a natural number);
`q` is the discount factor (0 ≤ q < 1). `P` (the game) is
optional — omit it to use the default 2×2 stage game.

    {
      "T": 3,
      "q": "1/2",
      "W": { "uF_own": "7/2", "uF_partner": "5", "v": "3/2",
             "Lf": "5", "M0": "6" },
      "P": { "0": {"coop":"7/2","dev":"2","sucker":"1","safe":"2"},
             "1": {"coop":"7/2","dev":"2","sucker":"1","safe":"2"} }
    }

Mechanism fields: `uF_own` / `uF_partner` — reward values for
the rewarded party and its partner; `v` — the punishment-phase
value; `Lf` — the forfeit; `M0` — the cap bounding all values.

Things to try: lower `q` until certification fails (deterrence
needs patience); set `v` above `uF_own` and watch the static
contract refuse by name; vary `T` and observe that the window
is data, not a limit.

## Reading the output

Each run shows, in order: the **admissibility contract**
(finitely many named inequalities on the specification itself),
then the **certificate clauses** at your (T, q), then the
result. An acceptance printed by this program means the input
lies on the acceptance side of the decision surface mirrored
from the formally verified checker — **it is not itself a
kernel certificate**. The frozen examples marked
`KERNEL WITNESS: VERIFIED` correspond to actual generated Coq
certificates that compile and pass `coqchk` with
`Axioms: <none>`. Visitor-supplied specifications acquire that
status through formal certification:

    TRY THE DECISION SURFACE  →  REQUEST KERNEL CERTIFICATION

The first is this program. The second is the proprietary
capability.

## The guarantee, precisely

When formal certification accepts a point, the kernel theorem
(`tg_checked_causal_deviation_secure_eps`) establishes: for
every legal history-reactive deviation strategy, every player,
and every ε > 0, there exists a sufficiently long horizon
beyond which deviation gains no more than ε over compliance
against the mediated enforcement machine. What is checked to
obtain it: the admissibility contract and the certificate
point. Nothing else. Full details: the white paper, §3–§6 and
the technical appendix.

## License & contact

`ucfgutt_gametheory_demo.py` is © 2023–2026 Michael Fillippini,
released under **Apache-2.0** (SPDX header in the file). The
theorem library, proofs, and certifying compiler are separate
proprietary works (Research & Evaluation v1.1, non-commercial)
and are **not** part of this distribution.

Contact & further material: https://relationalexistence.com
