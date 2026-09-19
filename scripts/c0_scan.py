#!/usr/bin/env python3
"""Numerical companion to the Lean module Lean4LPD.Constants.C0.

Evaluates, in floating point, the constant c_0 of the truncation-error theorem
(apd:thm:one_step_truncation_error, apd:eq:c0), which sets the time threshold
    t_0 = 1 / (c_0 * Gamma * (k_h - 1) * alpha):

    c_0 = (r+1)/r * exp[ (9/4)(m*+1) / (r*Gamma) ] * (1 + B)^(1/(m*+1)),   B = 4e*beta.

A triple (r, m*, Gamma) is admissible (the Lean predicate `Admissible`) when
    r >= max( 1, m*, 8(m*+1)^2 / Gamma ).
The remaining step-count condition of the theorem, r >= 8 e^2 w_2 alpha t with
w_2 = k_o + k_h - 1, constrains alpha*t rather than the triple.  It is what bounds B:
with beta = 2 e w_2 sin(dt) and sin(dt) <= alpha t / r it gives beta <= 1/(4e), i.e. B <= 1.

The Lean module proves  c_0 <= (384/275) sqrt(2) < 2  for admissible triples with
m* >= 1, r >= 5 and 0 <= B <= 1, and proves that neither m* >= 1 nor r >= 5 can be dropped.
This script

  (1) evaluates c_0 at the witness points of the Lean module (admissible, c_0 > 2);
  (2) evaluates c_0 on an integer grid of (m*, Gamma), m* = 0, 1, ..., at the smallest
      admissible integer r, and prints the grid maximum with and without the
      hypotheses m* >= 1 and r >= 5;
  (3) prints the supremum of c_0 over the admissible set as a function of m*;
  (4) checks that the witness (r, m*, Gamma) = (1, 1, 32) is compatible with the
      remaining conditions of the theorem;
  (5) tabulates c_0 against the effective layer count Upsilon*Gamma of the pth-order
      product formula.

The statements themselves are proved in Lean; nothing here is part of a proof.

Run:  python3 scripts/c0_scan.py
"""
import math

E = math.e


def c0(r, m, G, four_e_beta):
    """The constant c_0 of apd:eq:c0 (Lean: `cZero r m G B` with B = four_e_beta)."""
    return (r + 1) / r * math.exp(2.25 * (m + 1) / (r * G)) * (1 + four_e_beta) ** (1 / (m + 1))


def admissible(r, m, G):
    """The Lean predicate `Admissible r m G`."""
    return r >= 1 and m >= 0 and G > 0 and m <= r and 8 * (m + 1) ** 2 <= r * G


def r_min(m, G, r_floor=1):
    """Smallest integer r >= r_floor such that (r, m, G) is admissible.

    The condition r >= 8 e^2 w_2 alpha t is satisfiable at any r once alpha*t is
    small enough, so it does not raise this minimum.  See `feasibility_check` below.
    """
    return max(m, math.ceil(8 * (m + 1) ** 2 / G), r_floor)


def scan(four_e_beta, m_max=50, G_max=64, r_floor=1, m_min=0):
    """Maximum of c_0 over the grid m_min <= m* <= m_max, 1 <= Gamma <= G_max, r = r_min."""
    worst, arg = 0.0, None
    for m in range(m_min, m_max + 1):
        for G in range(1, G_max + 1):
            r = r_min(m, G, r_floor)
            v = c0(r, m, G, four_e_beta)
            if v > worst:
                worst, arg = v, (m, G, r)
    return worst, arg


def sup_c0(m, four_e_beta=1.0):
    """Supremum of c_0 over admissible (r, Gamma) at fixed m* (real r and Gamma).

    c_0 decreases in r and in Gamma, so the supremum sits where both constraints on r
    are active:  r = max(1, m*)  and  r*Gamma = 8(m*+1)^2.
    """
    r = max(1, m)
    return c0(r, m, 8 * (m + 1) ** 2 / r, four_e_beta)


def feasibility_check(m=1, G=32, k_o=1, k_h=2):
    """Check that a witness is compatible with the remaining conditions of the theorem."""
    w2 = k_o + k_h - 1
    r = r_min(m, G)
    # r >= 8 e^2 w2 alpha t  <=>  alpha t <= r / (8 e^2 w2)
    at_cap = r / (8 * E**2 * w2)
    # t < 1/(c Gamma (k_h-1) alpha)  <=>  alpha t < 1/(c Gamma (k_h-1)),  evaluated at c = 2
    at_t0 = 1 / (2 * G * (k_h - 1))
    # the point is reachable iff some alpha*t satisfies BOTH bounds
    return r, at_cap, at_t0, min(at_cap, at_t0)


WITNESSES = [
    # (r, m*, Gamma, B), Lean theorem, what it shows
    ((1, 1, 32, 0), "two_lt_cZero_of_admissible", "r >= 5 is needed, even at B = 0"),
    ((4, 1, 8, 1), "two_lt_cZero_of_admissible_four", "r >= 4 is not enough"),
    ((5, 0, 2, 1), "two_lt_cZero_of_m_zero", "m* >= 1 is needed"),
    ((2, 2, 36, 1), "two_lt_cZero_of_m_two", "m* >= 2 alone is not enough (m* >= 3 is)"),
    ((1, 0, 8, 1), "cZero_eq_four_mul_exp_at_worst", "maximum 4 e^(9/32) over the admissible set"),
]


if __name__ == "__main__":
    print("Range of B = 4e*beta under the step-count condition r >= 8 e^2 w_2 alpha t")
    print(f"  beta <= 1/(4e) = {1/(4*E):.6f}   =>   4e*beta <= {4*E/(4*E):.1f}")
    print("  (The rows with 4e*beta <= 1/2 below correspond to r >= 16 e^2 w_2 alpha t.)\n")

    print("Witness points of Lean4LPD.Constants.C0 (each point is admissible, c_0 > 2)")
    for (r, m, G, B), name, what in WITNESSES:
        assert admissible(r, m, G)
        v = c0(r, m, G, B)
        assert v > 2
        print(f"  (r, m*, Gamma, B) = ({r}, {m}, {G:2d}, {B}) : c_0 = {v:.4f}   {name}: {what}")
    print()

    print("Grid maximum of c_0 (0 <= m* <= 50, r at its smallest admissible integer value)")
    for feb, label in [(0.5, "4e*beta <= 1/2"),
                       (1.0, "4e*beta <= 1  "),
                       (0.0, "beta -> 0     ")]:
        zero, arg0 = scan(feb, G_max=64)
        box, _ = scan(feb, G_max=6, m_min=1)
        wide, arg = scan(feb, G_max=64, m_min=1)
        first = next(((G, r_min(1, G), c0(r_min(1, G), 1, G, feb))
                      for G in range(1, 65) if c0(r_min(1, G), 1, G, feb) > 2), None)
        print(f"  {label}")
        print(f"    max c_0, m* >= 0, Gamma <= 64       : {zero:.4f}  at m*={arg0[0]}, Gamma={arg0[1]}, r={arg0[2]}")
        print(f"    max c_0, m* >= 1, Gamma <= 6        : {box:.4f}")
        print(f"    max c_0, m* >= 1, Gamma <= 64       : {wide:.4f}  at m*={arg[0]}, Gamma={arg[1]}, r={arg[2]}")
        print(f"    smallest Gamma with c_0 > 2 at m*=1 : {first}   (Gamma, r, c_0)")
    print()

    print("Supremum of c_0 over the admissible set as a function of m*  (4e*beta = 1)")
    for m in range(0, 5):
        v = sup_c0(m)
        print(f"  m* = {m} : sup c_0 = {v:.4f}   {'> 2' if v > 2 else '<= 2'}")
    print()

    print("The witness (r, m*, Gamma) = (1, 1, 32) is compatible with the other conditions:")
    r, at_cap, at_t0, both = feasibility_check()
    print(f"  m*=1, Gamma=32, k_o=1, k_h=2  =>  r_min = {r}")
    print(f"  r >= 8e^2 w_2 alpha t  needs   alpha*t <= {at_cap:.5f}")
    print(f"  t < t_0 (with c_0=2)   needs   alpha*t <  {at_t0:.5f}")
    print(f"  both hold for any alpha*t <= {both:.5f} (e.g. alpha*t = 0.005),")
    print(f"  so the point is reachable, not vacuous.\n")
    print("  For scale: a k_h-local Hamiltonian whose interaction graph has degree d needs")
    print("  about d disjoint-support layers, so Gamma = 32 corresponds to degree about 31,")
    print("  or to Upsilon*Gamma for a higher-order formula over fewer groups.\n")

    print("Under the hypotheses of cZero_le_two (admissible, m* >= 1, r >= 5):")
    for feb, label in [(0.5, "4e*beta <= 1/2"), (1.0, "4e*beta <= 1")]:
        for Gm in (64, 512):
            w, _ = scan(feb, G_max=Gm, r_floor=5, m_min=1)
            print(f"  {label}, Gamma <= {Gm:3d}, r >= 5 :  max c_0 = {w:.4f}   {'OK' if w <= 2 else 'FAILS'}")
    print(f"  proved bound (cZero_le_two_sharp): (384/275)*sqrt(2) = {384/275*math.sqrt(2):.4f}")
    w, a = scan(1.0, G_max=64, r_floor=5)
    print(f"  without m* >= 1 (4e*beta <= 1)     :  max c_0 = {w:.4f}   at m*={a[0]}, Gamma={a[1]}, r={a[2]}")


# ---------------------------------------------------------------------------
# The effective layer count.
#
# For the pth-order product formula, apd:thm:one_step_truncation_error is applied
# with Gamma replaced by Upsilon*Gamma, Upsilon = 2*5^{p/2-1} (apd:eq:suzuki,
# apd:thm:lightcone).  The layer count entering c_0 is therefore Upsilon*Gamma,
# and the table below evaluates c_0 against it.  Without the hypothesis r >= 5,
# c_0 exceeds 2 already for the second-order formula at Gamma = 4; with it, or
# with Upsilon*Gamma <= 7 (cZero_le_two_of_gamma_le_seven), c_0 <= 2.
# ---------------------------------------------------------------------------

def upsilon(p):
    """Depth overhead of the pth-order recursion."""
    return 2 * 5 ** (p / 2 - 1)


def gamma_upsilon_table(four_e_beta=1.0, m=1):
    """c_0 at the smallest admissible integer r, as a function of the product formula order."""
    rows = []
    for p in (2, 4, 6):
        U = upsilon(p)
        for G in (1, 2, 4, 6):
            Geff = U * G
            r = r_min(m, Geff)
            rows.append((p, U, G, Geff, r, c0(r, m, Geff, four_e_beta)))
    return rows


if __name__ == "__main__":
    print("\n" + "=" * 72)
    print("c_0 against the effective layer count Upsilon*Gamma  (m* = 1, 4e*beta = 1)")
    print("=" * 72)
    print("  r_min is the smallest admissible integer r, without the hypothesis r >= 5;")
    print("  the last column imposes r >= 5.\n")
    print(f"  {'p':>2} {'Upsilon':>8} {'Gamma':>6} {'eff':>6} {'r_min':>6} {'c_0':>8} {'c_0 (r>=5)':>11}")
    for p, U, G, Geff, r, v in gamma_upsilon_table(1.0):
        flag = "  <-- exceeds 2" if v > 2 else ""
        v5 = c0(max(r, 5), 1, Geff, 1.0)
        print(f"  {p:>2} {U:>8.0f} {G:>6} {Geff:>6.0f} {r:>6} {v:>8.4f} {v5:>11.4f}{flag}")
    print("\n  Upsilon = 10 already at p = 4, so for p >= 4 the effective layer count")
    print("  exceeds 7 for every Gamma: the cap of cZero_le_two_of_gamma_le_seven is not")
    print("  available, and c_0 <= 2 rests on r >= 5 (or on m* >= 3).")
