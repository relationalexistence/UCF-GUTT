#!/usr/bin/env python3
#
#  Copyright 2023-2026 Michael Fillippini
#  SPDX-License-Identifier: Apache-2.0
#
# ═════════════════════════════════════════════════════════════
#  UCF/GUTT GameTheory — public demonstrator
#
#     strategic specification -> formal certification ->
#     machine-checked causal-security guarantee
#
#  This tool shows WHAT the certification system decides, using
#  the same exact rational arithmetic as the formally verified
#  checker.  The underlying theorem library (Coq 8.18, zero
#  axioms, kernel-checked with `coqchk`: "Axioms: <none>") and
#  the certifying compiler that emits machine-checked
#  certificates are the private development stack; this
#  demonstrator contains neither.  What it faithfully
#  reproduces is the DECISION SURFACE: admissibility of a
#  strategic specification, acceptance/refusal of a
#  certificate point, and the precise guarantee certified.
#
#  Licensed under Apache-2.0.  The private theorem/certification
#  stack is not part of this distribution.  Contact:
#  https://relationalexistence.com
# ═════════════════════════════════════════════════════════════
import sys, json, argparse
from fractions import Fraction as F

def Q(x): return F(x)

# ── the certified decision mathematics (exact rationals) ─────
def geom_sum(q, n):        # 1 + q + ... + q^(n-1)
    s = F(0)
    for _ in range(n): s = 1 + q * s
    return s

def qpow(q, n):
    r = F(1)
    for _ in range(n): r *= q
    return r

def admissibility(W, P):
    """The static contract.  Returns [(obligation, ok, detail)].
    Mirrors the mechanized contract obligation-for-obligation."""
    rows = []
    ok_all = True
    def row(name, ok, detail):
        nonlocal ok_all
        rows.append((name, ok, detail)); ok_all = ok_all and ok
    fs = all(0 <= W[k] <= W["M0"] for k in
             ("uF_own", "uF_partner", "v", "Lf"))
    row("MechanismFeasible", fs,
        "all enforcement values within [0, M0]")
    row("MechRewardMargins.pos", W["uF_own"] > 0,
        "0 < uF_own  (reward is real)")
    row("MechRewardMargins.v_le", W["v"] <= W["uF_own"],
        "v <= uF_own  (punishment does not beat cooperation)")
    row("MechRewardMargins.own_le", W["uF_own"] <= W["uF_partner"],
        "uF_own <= uF_partner  (no incentive to trigger reward)")
    gf = all(0 <= P[i][c] <= W["M0"]
             for i in (0, 1) for c in ("coop","dev","sucker","safe"))
    row("GamePayoffFeasible", gf, "all game cells within [0, M0]")
    cf = all(W["uF_own"] <= P[i]["coop"] for i in (0, 1))
    row("CoopRewardFloor", cf,
        "uF_own <= cooperative payoff (both players)")
    return rows, ok_all

def certificate_check(T, W, P, q):
    """The dynamic certificate at (T, q).  Mirrors the verified
    Boolean checker `parametric_checkT` clause-for-clause."""
    A = max(P[i][c] for i in (0, 1) for c in ("dev","safe"))
    C = min(P[i]["coop"] for i in (0, 1))
    G1, G2 = geom_sum(q, T + 1), geom_sum(q, T + 2)
    rows = []
    rows.append(("range: 0 <= q < 1", 0 <= q < 1))
    rows.append(("normal-deviation clause",
                 A + q * (W["v"] * G1) < C * G2))
    rows.append(("reward-deviation clause",
                 W["M0"] + q * (W["v"] * G1) < W["uF_partner"] * G2))
    bys = True
    for k in range(T + 1):
        lhs = qpow(q, T + 1) * q * (W["M0"] - W["uF_partner"])
        rhs = (1 - q) * (W["Lf"] * geom_sum(q, T - k + 1)
               + qpow(q, T - k + 1) * (W["uF_partner"] * geom_sum(q, k + 1))
               - W["M0"] - q * (W["v"] * G1))
        bys = bys and (lhs <= rhs)
    rows.append(("bystander clauses (k = 0..%d)" % T, bys))
    return rows, all(ok for _, ok in rows)

THEOREM = """
  FORMAL CERTIFICATION OF THIS ACCEPTED POINT ESTABLISHES
  (kernel theorem: tg_checked_causal_deviation_secure_eps —
  Coq 8.18, zero axioms, coqchk: "Axioms: <none>")

  For THIS game, THIS mechanism, punishment window T = {T},
  discount q = {q}:

  For every legal history-reactive deviation strategy, every
  player, and every epsilon > 0, there exists a sufficiently
  long horizon beyond which deviation gains no more than
  epsilon over compliance against the mediated enforcement
  machine.

  What was checked to obtain it: the admissibility contract
  above (finitely many exact inequalities) and this certificate
  point.  Nothing else.
"""

EXAMPLES = {
  "v04-baseline": dict(T=4, q="1/2", kernel_witness=True,
    W=dict(uF_own="14/5", uF_partner="7/2", v="1", Lf="4", M0="4"),
    note="The original sealed configuration."),
  "alt-T2": dict(T=2, q="1/2", kernel_witness=True,
    W=dict(uF_own="7/2", uF_partner="5", v="3/2", Lf="5", M0="6"),
    note="Alternative mechanism, short punishment window."),
  "alt-T3": dict(T=3, q="1/2", kernel_witness=True,
    W=dict(uF_own="7/2", uF_partner="5", v="3/2", Lf="5", M0="6"),
    note="Same mechanism, window T = 3."),
  "alt-T6": dict(T=6, q="1/2", kernel_witness=True,
    W=dict(uF_own="7/2", uF_partner="5", v="3/2", Lf="5", M0="6"),
    note="Same mechanism, long window: T is data, not a limit."),
  "invalid-mechanism": dict(T=3, q="1/2",
    W=dict(uF_own="1", uF_partner="5", v="3/2", Lf="5", M0="6"),
    note="Punishment pays better than cooperation: REFUSED at "
         "the margin the formal development discovered."),
  "admissible-but-uncertifiable": dict(T=4, q="1/10",
    W=dict(uF_own="7/2", uF_partner="5", v="3/2", Lf="5", M0="6"),
    note="Sound mechanism, but the future is discounted too "
         "heavily for deterrence: certificate refused at this q."),
}
DEFAULT_GAME = {0: dict(coop="7/2", dev="2", sucker="1", safe="2"),
                1: dict(coop="7/2", dev="2", sucker="1", safe="2")}

def run(name, spec):
    W = {k: Q(v) for k, v in spec["W"].items()}
    P = {i: {c: Q(v) for c, v in
             spec.get("P", DEFAULT_GAME)[i].items()} for i in (0, 1)}
    T_raw = spec["T"]
    if not isinstance(T_raw, int) or isinstance(T_raw, bool) \
       or T_raw < 0:
        print("═" * 62)
        print(" %s" % name)
        print(" INVALID INPUT: T must be a natural number")
        print(" (the formal theorem has T : nat); got %r." % T_raw)
        return
    T, q = T_raw, Q(spec["q"])
    print("═" * 62)
    print(" %s   (T = %d, q = %s)" % (name, T, q))
    if spec.get("note"): print("   %s" % spec["note"])
    print("─" * 62)
    print(" ADMISSIBILITY (the static contract)")
    rows, adm = admissibility(W, P)
    for n, ok, d in rows:
        print("   [%s] %-24s %s" % ("PASS" if ok else "FAIL", n, d))
    if not adm:
        print("─" * 62)
        print(" RESULT: INADMISSIBLE — no certificate exists for this")
        print(" specification; the failing obligation above names why.")
        return
    print(" CERTIFICATE at q = %s" % q)
    crows, cert = certificate_check(T, W, P, q)
    for n, ok in crows:
        print("   [%s] %s" % ("PASS" if ok else "FAIL", n))
    print("─" * 62)
    if cert:
        print(" RESULT: DEMONSTRATOR CHECK ACCEPTED")
        print()
        print(" This input lies on the acceptance side of the")
        print(" exact-rational decision surface mirrored from the")
        print(" formally verified checker.  This Python run is NOT")
        print(" itself a kernel certificate; formal certification")
        print(" requires the private certifying compiler and Coq")
        print(" verification.")
        if spec.get("kernel_witness"):
            print()
            print(" KERNEL WITNESS: VERIFIED — a generated Coq")
            print(" certificate for this exact configuration compiles")
            print(" and passes coqchk (Axioms: <none>).")
        print(THEOREM.format(T=T, q=q))
    else:
        print(" RESULT: admissible specification, certificate REFUSED")
        print(" at this (T, q) point — the failing clause above is the")
        print(" exact inequality that could not be established.")

def main():
    ap = argparse.ArgumentParser(
        description="UCF/GUTT GameTheory certification demonstrator")
    ap.add_argument("--example", choices=sorted(EXAMPLES))
    ap.add_argument("--spec", help="JSON: {T, q, W{...}, P{0:{},1:{}}?}")
    ap.add_argument("--list", action="store_true")
    ap.add_argument("--all", action="store_true")
    a = ap.parse_args()
    if a.list:
        for k, v in EXAMPLES.items():
            print("%-28s %s" % (k, v["note"]))
    elif a.all:
        for k in sorted(EXAMPLES): run(k, EXAMPLES[k])
    elif a.example:
        run(a.example, EXAMPLES[a.example])
    elif a.spec:
        s = json.load(open(a.spec))
        if "P" in s: s["P"] = {int(k): v for k, v in s["P"].items()}
        run(a.spec, s)
    else:
        ap.print_help()
        print("\nStart with:  python3 %s --all" % sys.argv[0])

if __name__ == "__main__":
    main()
