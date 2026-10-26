"""Check the cluster-graph lemma (Theorem A) for m = 5..14 by enumerating count matrices.

Graph: three clusters of size m, inner weight 1, inter-cluster weight beta (no perturbation).
A vertex set is described by (u_1, u_2, u_3), u_i = |X cap C_i|; a 3-partition by a 3x3
matrix N with column sums m (N[k][i] = |P_k cap C_i|). Exact rational arithmetic.
Checks, for beta = 1/(2m) + 1/4 * (2(m-1)/(3m^2) - 1/(2m)) and for beta just inside both ends:
  (1) every cut with >= 2 vertices on each side is heavier than the degree D;
  (2) the clusters are the unique minimum-weight 3-partition;
  (3) the clusters' pair weight m^2 beta is below lambda = D (hardness).
"""
import itertools
from fractions import Fraction as Fr


def comps(m):
    return [(a, b, m - a - b) for a in range(m + 1) for b in range(m + 1 - a)]


def check(m, beta):
    n = 3 * m
    D = (m - 1) + 2 * m * beta
    ok1 = True
    for u in itertools.product(range(m + 1), repeat=3):
        s = sum(u)
        if 2 <= s <= n - 2:
            d = (1 - beta) * sum(x * (m - x) for x in u) + beta * s * (n - s)
            ok1 &= d > D
    C = comps(m)
    best = None; count = 0
    target = 3 * m * m * beta
    for c1 in C:
        for c2 in C:
            for c3 in C:
                rows = [(c1[k], c2[k], c3[k]) for k in range(3)]
                sizes = [sum(r) for r in rows]
                if min(sizes) == 0:
                    continue
                alpha_cut = sum(Fr(m * (m - 1), 2) - sum(Fr(r[i] * (r[i] - 1), 2) for r in rows)
                                for i in range(3))
                total_cut = Fr(n * (n - 1), 2) - sum(Fr(s * (s - 1), 2) for s in sizes)
                W = alpha_cut + beta * (total_cut - alpha_cut)
                if best is None or W < best:
                    best, count = W, 1
                elif W == best:
                    count += 1
    # the cluster partition appears 3! = 6 times (labelled rows)
    ok2 = best == target and count == 6
    ok3 = m * m * beta < D
    return ok1, ok2, ok3


def main():
    allok = True
    for m in range(5, 15):
        lo, hi = Fr(1, 2 * m), Fr(2 * (m - 1), 3 * m * m)
        for beta in (lo + (hi - lo) / 1000, lo + (hi - lo) / 4, hi - (hi - lo) / 1000):
            r = check(m, beta)
            allok &= all(r)
            print(f"m={m:2d} beta={float(beta):.5f}: nontrivial cuts > D {r[0]}, clusters unique optimum {r[1]}, hard {r[2]}")
    print("RESULT:", "all checks passed" if allok else "SOME CHECK FAILED")


if __name__ == "__main__":
    main()
