"""Lemma 7 (merging a Gomory-Hu side) on random graphs.

For every optimum (A, B, C), every Gomory-Hu tree edge e = (s, t) and its side X
containing s, with s in part P: if X contains neither all of either other part, then
(P + X, Q - X, R - X) must again be an optimum. Merges that change the partition
(X not inside P) are counted and checked; merges with X inside P change nothing and are
counted separately.

Family: as in exp1 (mixed planar/general, real/integer), 6-11 vertices, 20000 graphs.
Runtime: under a minute.
"""
import sys, time
import numpy as np
from cutlib import (cut_table, tolerance, optimum, labelings, gomory_hu_tree,
                    fundamental_side, random_instance)


def main(trials=20000):
    t0 = time.time()
    rng = np.random.default_rng(7)
    merges = viol = trivial = 0
    for t in range(trials):
        n, E = random_instance(t, rng, 6, 11)
        d, tol = cut_table(n, E), tolerance(E)
        opt, idx, W = optimum(n, E, tol)
        L, M = labelings(n)
        tree = gomory_hu_tree(n, d, tol)
        for i in idx:
            parts = [int(x) for x in M[i]]
            for x, y, _ in tree:
                for s, tt in ((x, y), (y, x)):
                    X = fundamental_side(n, tree, s, tt)
                    p = next(k for k in range(3) if (parts[k] >> s) & 1)
                    others = [parts[k] for k in range(3) if k != p]
                    if any((Q & X) == Q for Q in others):
                        continue  # hypothesis of Lemma 7 fails
                    if (X & parts[p]) == X:
                        trivial += 1  # X already inside P: the merge changes nothing
                        continue
                    new = [parts[p] | X] + [Q & ~X for Q in others]
                    w = (d[new[0]] + d[new[1]] + d[new[2]]) / 2.0
                    merges += 1
                    viol += w > opt + tol
    print(f"graphs {trials}; (optimum, tree side) pairs satisfying the hypothesis: "
          f"{merges + trivial}, of which {trivial} trivial (X inside P)")
    print(f"non-trivial merges tested {merges}, not optimal {viol}")
    print(f"time {time.time() - t0:.0f} s")
    print("RESULT:", "all checks passed" if viol == 0 else f"{viol} VIOLATIONS")
    return viol


if __name__ == "__main__":
    sys.exit(1 if main(int(sys.argv[1]) if len(sys.argv) > 1 else 20000) else 0)
