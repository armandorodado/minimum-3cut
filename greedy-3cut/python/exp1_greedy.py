"""Theorem 1, Corollaries 2-3 and Proposition 5 on random graphs.

For every global minimum-weight cut S and every 3-partition (A, B, C), with each part
in the role of A, checks
    greedy(S) <= max(lambda + d(A), W(A, B, C))                  (Theorem 1)
    greedy(S) <= 4/3 OPT                                          (Corollary 3)
and, whenever greedy(S) > OPT for some S, that every optimum is hard
(all three pair weights below lambda; Corollary 2), together with the
bounds of Proposition 5 for every hard optimum.

Family: planar (Delaunay, edges kept w.p. 0.8) and general (G(n, 0.45)) graphs,
real (uniform [1,10]) and integer (1..5) weights, 400 graphs per combination.
Runtime: a few seconds.
"""
import sys, time
import numpy as np
from cutlib import (cut_table, tolerance, global_min_cuts, greedy_value, optimum,
                    labelings, is_hard, pair_weight, random_planar, random_general, to_instance)


def main(per_config=400):
    t0 = time.time()
    totals = dict(graphs=0, min_cuts=0, thm1_checks=0, thm1_viol=0, cor3_viol=0,
                  inexact_graphs=0, inexact_not_all_hard=0, hard_optima=0, prop5_viol=0)
    configs = [(True, False, 6, 11), (True, True, 6, 11), (False, False, 6, 10), (False, True, 6, 10)]
    for planar, integer, lo, hi in configs:
        rng = np.random.default_rng(100 + 2 * planar + integer)
        for _ in range(per_config):
            n = int(rng.integers(lo, hi + 1))
            G = random_planar(n, 0.8, rng, integer) if planar else random_general(n, 0.45, rng, integer)
            n, E = to_instance(G)
            d, tol = cut_table(n, E), tolerance(E)
            lam, cuts = global_min_cuts(n, d, tol)
            opt, idx, W = optimum(n, E, tol)
            _, M = labelings(n)
            dA = d[M]                                   # d of each part, shape (rows, 3)
            totals["graphs"] += 1
            inexact = False
            for S in cuts:
                g = greedy_value(n, d, S)
                assert g >= opt - tol
                totals["min_cuts"] += 1
                bound = np.maximum(lam + dA, W[:, None])  # each part in the role of A
                totals["thm1_checks"] += bound.size
                totals["thm1_viol"] += int((g > bound + tol).sum())
                totals["cor3_viol"] += int(g > 4 * opt / 3 + tol)
                inexact |= g > opt + tol
            if inexact:
                totals["inexact_graphs"] += 1
                if not all(is_hard(d, M[i], lam, tol) for i in idx):
                    totals["inexact_not_all_hard"] += 1
            for i in idx:
                if is_hard(d, M[i], lam, tol):
                    totals["hard_optima"] += 1
                    A, B, C = (int(x) for x in M[i])
                    pws = [pair_weight(d, A, B), pair_weight(d, A, C), pair_weight(d, B, C)]
                    ok = (min(pws) > 0 and all(lam - tol <= d[X] < 2 * lam - tol for X in (A, B, C))
                          and 1.5 * lam - tol <= opt < 3 * lam)
                    totals["prop5_viol"] += not ok
    for k, v in totals.items():
        print(f"{k:24s} {v}")
    print(f"time {time.time() - t0:.0f} s")
    bad = totals["thm1_viol"] + totals["cor3_viol"] + totals["inexact_not_all_hard"] + totals["prop5_viol"]
    print("RESULT:", "all checks passed" if bad == 0 else f"{bad} VIOLATIONS")
    return bad


if __name__ == "__main__":
    sys.exit(1 if main(int(sys.argv[1]) if len(sys.argv) > 1 else 400) else 0)
