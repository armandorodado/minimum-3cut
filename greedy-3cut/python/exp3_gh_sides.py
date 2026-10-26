"""F(T) = OPT on random and structured graphs.

F(T) is the least weight of a 3-partition with a Gomory-Hu side as a part (the first
stage of Kapoor's algorithm). The paper shows F(T) > OPT can happen (Theorem 9); this
script records how often it happens on unstructured inputs.

Families:
  random      800 graphs, mixed planar/general and real/integer weights, 6-10 vertices;
  structured  1600 attempts, near-complete / circulant / three-cluster / wheel graphs
              with 7-10 vertices (Gomory-Hu trees are mostly stars).
Runtime: a few seconds.
"""
import sys, time
import numpy as np
from cutlib import (cut_table, tolerance, optimum, gomory_hu_tree, kapoor_F, labelings,
                    global_min_cuts, is_hard, random_instance, structured, to_instance)


def check(n, E):
    d, tol = cut_table(n, E), tolerance(E)
    opt, idx, _ = optimum(n, E, tol)
    tree = gomory_hu_tree(n, d, tol)
    F = kapoor_F(n, d, tree)
    lam, _ = global_min_cuts(n, d, tol)
    _, M = labelings(n)
    hard = all(is_hard(d, M[i], lam, tol) for i in idx)
    star = max(sum(1 for a, b, _ in tree if v in (a, b)) for v in range(n)) == n - 1
    return F > opt + tol, hard, star


def main():
    t0 = time.time()
    rng = np.random.default_rng(11)
    fails = 0
    for t in range(800):
        f, _, _ = check(*random_instance(t, rng, 6, 10))
        fails += f
    print(f"random:     graphs 800, F(T) > OPT in {fails}")
    total_fail = fails
    rng = np.random.default_rng(5)
    stats = {}
    for t in range(1600):
        kind = ["near-complete", "circulant", "clusters", "wheel"][t % 4]
        G = structured(kind, int(rng.integers(7, 11)), rng)
        if G is None:
            continue
        f, hard, star = check(*to_instance(G))
        s = stats.setdefault(kind, [0, 0, 0, 0])
        s[0] += 1; s[1] += f; s[2] += hard; s[3] += star
        total_fail += f
    n_struct = sum(s[0] for s in stats.values())
    for k, (a, b, c, e) in stats.items():
        print(f"structured: {k:14s} graphs {a:4d}, F(T) > OPT in {b}, all optima hard {c}, star tree {e}")
    print(f"structured: total graphs {n_struct}")
    print(f"time {time.time() - t0:.0f} s")
    print("RESULT:", f"F(T) > OPT in {total_fail} of {800 + n_struct} graphs")
    return 0


if __name__ == "__main__":
    sys.exit(main())
