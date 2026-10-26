"""k-cluster version of Lemmas A1/A3, checked by enumerating count matrices (exact integers).

Graph: k clusters of size m, inner weight 1, inter-cluster weight beta = p/q (rational).
A k-partition is described by a k x k matrix N (N[r][i] = |P_r cap C_i|, column sums m,
no empty row). Weights are scaled by q to integers. Checks for a given (k, m, beta):
  (1) every cut with >= 2 vertices on each side is heavier than the degree D;
  (2) the clusters are the unique minimum-weight k-partition;
  (3) every pair weight m^2 beta is below lambda = D (hardness);
and reports the best k-partition having a single vertex as a part, relative to OPT.
Usage: python3 kcluster_check.py k m p q
"""
import itertools, sys
import numpy as np
from math import comb


def comps(m, k):
    out = []
    for c in itertools.combinations(range(m + k - 1), k - 1):
        parts, prev = [], -1
        for x in c:
            parts.append(x - prev - 1); prev = x
        parts.append(m + k - 2 - prev)
        out.append(parts)
    return np.array(out, dtype=np.int64)


def main(k, m, p, q):
    n = k * m
    # integer weights: inner q, cross p   (beta = p/q)
    Dq = (m - 1) * q + (k - 1) * m * p
    # (1) cuts: U described by u_i in 0..m
    ok1 = True
    for u in itertools.product(range(m + 1), repeat=k):
        s = sum(u)
        if 2 <= s <= n - 2:
            inner = sum(x * (m - x) for x in u)
            d = (q - p) * inner + p * s * (n - s)
            ok1 &= d > Dq
    # (2) partitions
    C = comps(m, k)                 # each column: how cluster i splits over the k rows
    best = None; cnt = 0; best_single = None
    target = comb(k, 2) * m * m * p
    for first in range(len(C)):
        cols = [C[[first]]] + [C] * (k - 1)
        grids = np.meshgrid(*[np.arange(len(c)) for c in cols], indexing="ij")
        idx = [g.ravel() for g in grids]
        N = np.stack([cols[i][idx[i]] for i in range(k)], axis=2)   # (#, k rows, k clusters)
        sizes = N.sum(2)
        keep = (sizes > 0).all(1)
        N, sizes = N[keep], sizes[keep]
        inner_cut = k * comb(m, 2) - (N * (N - 1) // 2).sum((1, 2))
        total_cut = comb(n, 2) - (sizes * (sizes - 1) // 2).sum(1)
        W = q * inner_cut + p * (total_cut - inner_cut)
        mn = W.min()
        if best is None or mn < best:
            best, cnt = mn, int((W == mn).sum())
        elif mn == best:
            cnt += int((W == mn).sum())
        single = (sizes == 1).any(1)
        if single.any():
            ms = W[single].min()
            best_single = ms if best_single is None else min(best_single, ms)
    from math import factorial
    ok2 = best == target and cnt == factorial(k)
    ok3 = m * m * p < Dq
    print(f"k={k} m={m} beta={p}/{q}: nontrivial cuts > D {ok1}, clusters unique optimum {ok2}, "
          f"hard {ok3}; best with a singleton part / OPT = {best_single / best:.4f}; "
          f"limit 1+2(k-2)/(k(k-1)) = {1 + 2 * (k - 2) / (k * (k - 1)):.4f}")
    return ok1 and ok2 and ok3


if __name__ == "__main__":
    main(*(int(a) for a in sys.argv[1:]))
