"""Theorem 10, Corollaries 11-12 and the 5-vertex example of Section 6 (minimum k-cut).

R_k(S) is the least weight of a k-partition compatible with S (every part inside S or
inside its complement), for a global minimum-weight cut S.

Checks on random graphs with k+2..9 vertices (mixed planar/general, real/integer):
  (a) k = 4, 5: if some optimal k-partition has two parts joined by weight >= lambda,
      then R_k(S) = OPT_k for every global minimum-weight cut S          (Theorem 10);
  (b) k = 3, 4, 5: R_k(S) <= OPT_k + max(0, lambda - max pair weight), the best over
      optimal k-partitions                                               (Theorem 10);
  (c) k = 3, 4, 5: R_k(S) <= (1 + 2(k-2)/(k(k-1))) OPT_k                  (Corollary 11);
  (d) k = 4, 5: the weaker condition "the parts other than one are joined among
      themselves by weight >= lambda" does NOT suffice (violations are reported);
and verifies the 5-vertex example (4-cycle with unit weights, pendant edge of weight 2).
Runtime: a few seconds.
"""
import sys, time
import numpy as np
from cutlib import (cut_table, tolerance, global_min_cuts, k_partition_weights, compatible,
                    random_instance)


def analyse(n, k, E):
    d, tol = cut_table(n, E), tolerance(E)
    lam, cuts = global_min_cuts(n, d, tol)
    L, W = k_partition_weights(n, k, E)
    opt = float(W.min())
    R = [float(W[compatible(L, S, n)].min()) for S in cuts]
    best_pair = 0.0; weak = False
    for j in np.flatnonzero(W <= opt + tol):
        P = np.zeros((k, k))
        for u, v, w in E:
            a, b = L[j][u], L[j][v]
            if a != b:
                P[a, b] += w; P[b, a] += w
        best_pair = max(best_pair, P.max())
        for a in range(k):
            others = [x for x in range(k) if x != a]
            if sum(P[x, y] for x in others for y in others if x < y) >= lam - tol:
                weak = True
    return opt, lam, R, best_pair, weak, tol


def main():
    t0 = time.time()
    bad = 0
    for k, trials in ((3, 250), (4, 300), (5, 300)):
        rng = np.random.default_rng(10 + k)
        c_graphs = c_viol = b_cuts = b_viol = r_viol = w_cases = w_viol = 0
        worst = 1.0
        factor = 1 + 2 * (k - 2) / (k * (k - 1))
        for t in range(trials):
            n, E = random_instance(t, rng, k + 2, 9)
            opt, lam, R, bp, weak, tol = analyse(n, k, E)
            exact = all(r <= opt + tol for r in R)
            if bp >= lam - tol:
                c_graphs += 1; c_viol += not exact
            for r in R:
                b_cuts += 1
                b_viol += r > opt + max(0.0, lam - bp) + tol
                r_viol += r > factor * opt + tol
                worst = max(worst, r / opt)
            if k >= 4 and weak:
                w_cases += 1; w_viol += not exact
        bad += c_viol + b_viol + r_viol
        print(f"k={k}: graphs {trials}; condition holds in {c_graphs}, violations {c_viol}; "
              f"bound checked at {b_cuts} cuts, violations {b_viol}; factor {factor:.4f} "
              f"violations {r_viol} (worst R/OPT {worst:.4f})")
        if k >= 4:
            print(f"      weaker condition holds in {w_cases}, of which R_k > OPT_k in {w_viol}")
    # the example
    E = [(0, 1, 1.0), (1, 2, 1.0), (2, 3, 1.0), (3, 0, 1.0), (0, 4, 2.0)]
    d = cut_table(5, E)
    L, W = k_partition_weights(5, 4, E)
    lam = float(d[1:31].min())
    R = float(W[compatible(L, 1 << 4, 5)].min())
    ex_ok = lam == 2 and d[1 << 4] == 2 and W.min() == 4 and R == 5
    print(f"example: lambda = {lam:g} (attained by {{p}}: {d[1 << 4] == 2}), OPT_4 = {W.min():g}, "
          f"R_4({{p}}) = {R:g}  ->  {'as stated' if ex_ok else 'MISMATCH'}")
    bad += not ex_ok
    print(f"time {time.time() - t0:.0f} s")
    print("RESULT:", "all checks passed" if bad == 0 else f"{bad} VIOLATIONS")
    return bad


if __name__ == "__main__":
    sys.exit(1 if main() else 0)
