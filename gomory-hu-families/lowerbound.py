"""Graphs with one and the same unique Gomory-Hu tree but different hard optima.

G_pi = (three complete clusters of size m, inner weight ALPHA, all inter-cluster pairs
weight BETA, clusters given by the partition pi) + H, where H is a fixed graph
(independent of pi) with w_H(u, v) = a_u + a_v that makes all vertex degrees distinct.
Integer weights, exact arithmetic.

Checks, for several random balanced partitions pi:
  * every vertex degree is independent of pi;
  * every cut with at least two vertices on each side is heavier than every vertex degree,
    so the unique Gomory-Hu tree is the star centred at the vertex of largest degree, with
    edge weights equal to the leaf degrees (the same weighted tree for every pi);
  * the unique minimum-weight 3-partition is pi itself, and it is hard;
  * F(T) > OPT.
"""
import itertools, sys
import numpy as np
from cutlib import (cut_table, optimum, labelings, gomory_hu_tree, verify_cut_tree, kapoor_F,
                    pair_weight, edge_connectivity, popcount)

ALPHA, BETA = 1000, 140


def build(m, pi):
    n = 3 * m
    a = list(range(n))
    E = []
    for u, v in itertools.combinations(range(n), 2):
        w = (ALPHA if pi[u] == pi[v] else BETA) + a[u] + a[v]
        E.append((u, v, w))
    return n, E


def check(m, pi):
    n, E = build(m, pi)
    d = cut_table(n, E)
    deg = [int(d[1 << v]) for v in range(n)]
    sizes = np.array([popcount(S) for S in range(1 << n)])
    nontriv = (sizes >= 2) & (sizes <= n - 2)
    heavier = d[nontriv].min() > max(deg)
    opt, idx, _ = optimum(n, E, 0)
    _, M = labelings(n)
    parts = sorted(int(x) for x in M[idx[0]])
    target = sorted(sum(1 << v for v in range(n) if pi[v] == k) for k in range(3))
    lam = edge_connectivity(n, d)
    A, B, C = parts
    hard = max(pair_weight(d, A, B), pair_weight(d, A, C), pair_weight(d, B, C)) < lam
    tree = gomory_hu_tree(n, d, 0)
    verify_cut_tree(n, d, tree, 0); ok_tree = True  # raises on failure
    c = int(np.argmax(deg))
    star = sorted((min(x, y), max(x, y), int(w)) for x, y, w in tree) == \
        sorted((min(c, v), max(c, v), deg[v]) for v in range(n) if v != c)
    F = kapoor_F(n, d, tree)
    return deg, dict(nontrivial_cuts_heavier=bool(heavier), unique_opt=len(idx) == 1,
                     opt_is_pi=parts == target, hard=bool(hard), tree_ok=bool(ok_tree),
                     tree_is_star=bool(star), F_gt_OPT=bool(F > opt), OPT=opt, F=F, lam=lam)


def main(m=4, trials=6):
    rng = np.random.default_rng(1)
    degs = None; allok = True
    for t in range(trials):
        pi = rng.permutation(np.repeat(np.arange(3), m))
        deg, r = check(m, pi)
        same = degs is None or deg == degs
        degs = deg
        ok = same and all(v for k, v in r.items() if isinstance(v, bool))
        allok &= ok
        print(f"pi={''.join(map(str, pi))}  same degrees {same}  " +
              "  ".join(f"{k}={v}" for k, v in r.items()))
    print("RESULT:", "all checks passed" if allok else "SOME CHECK FAILED")
    return 0 if allok else 1


if __name__ == "__main__":
    sys.exit(main(*(int(a) for a in sys.argv[1:])))
