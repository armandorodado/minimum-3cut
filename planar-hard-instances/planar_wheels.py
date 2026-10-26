"""Planar version of Theorem A: three wheels joined by a ring of matching edges.

Each cluster is a wheel: a centre joined by spokes (weight s) to a rim cycle of m-1 vertices
(rim edges weight r). Each rim vertex has one external edge (weight x) to a rim vertex of a
neighbouring wheel: the first half of A's rim faces B, the second half faces C, and so on
around the ring, so the graph is planar. Weights are chosen so every vertex has degree
D = (m-1)s: r = ((m-2)s - x)/2.
Checks (exact integers): planarity, uniform degree, every non-trivial cut > D (so the star is
a Gomory-Hu tree; with a small per-vertex perturbation it becomes the unique one),
clusters = unique optimum, hardness, and the best 3-partition with a singleton part.
Usage: python3 planar_wheels.py m s x   (r is derived; m-1 must be even)
"""
import itertools, sys
import numpy as np
import networkx as nx
from cutlib import cut_table, labelings, partition_weights, edge_connectivity, popcount, pair_weight


def build(m, s, x):
    assert (m - 1) % 2 == 0
    r2 = (m - 2) * s - x                 # 2r, kept integer by doubling every weight
    E = {}
    def add(u, v, w):
        E[(min(u, v), max(u, v))] = E.get((min(u, v), max(u, v)), 0) + w
    rims = []
    for c in range(3):
        base = c * m
        centre, rim = base, list(range(base + 1, base + m))
        for v in rim:
            add(centre, v, 2 * s)
        for a, b in zip(rim, rim[1:] + rim[:1]):
            add(a, b, r2)
        rims.append(rim)
    h = (m - 1) // 2
    # A's second half faces B's first half, B's second half faces C's first, C's second faces A's first
    for c in range(3):
        mine = rims[c][h:]
        theirs = rims[(c + 1) % 3][:h]
        for a, b in zip(mine, reversed(theirs)):
            add(a, b, 2 * x)
    n = 3 * m
    return n, [(u, v, w) for (u, v), w in E.items()]


def main(m, s, x):
    n, E = build(m, s, x)
    G = nx.Graph(); G.add_weighted_edges_from(E)
    planar = nx.check_planarity(G)[0]
    d = cut_table(n, E)
    deg = [int(d[1 << v]) for v in range(n)]
    sizes = np.array([popcount(S) for S in range(1 << n)])
    nt = (sizes >= 2) & (sizes <= n - 2)
    L, M = labelings(n)
    W = partition_weights(n, E)
    opt = W.min(); idx = np.flatnonzero(W == opt)
    clusters = sorted(sum(1 << v for v in range(c * m, (c + 1) * m)) for c in range(3))
    is_cl = len(idx) == 1 and sorted(int(t) for t in M[idx[0]]) == clusters
    lam = edge_connectivity(n, d)
    A, B, C = clusters
    hard = max(pair_weight(d, A, B), pair_weight(d, A, C), pair_weight(d, B, C)) < lam
    single = (np.isin(M, [1 << v for v in range(n)])).any(1)
    print(f"m={m} s={s} x={x} (weights doubled): planar {planar}, degrees {sorted(set(deg))}, "
          f"non-trivial cuts > D {d[nt].min() > max(deg)}, clusters unique optimum {is_cl}, hard {hard}, "
          f"OPT {opt:.0f}, best with singleton part / OPT = {W[single].min() / opt:.4f}")


if __name__ == "__main__":
    main(*(int(a) for a in sys.argv[1:]))


def perturbed(m, s, x, eps=1e-3, perm=None):
    """Relabel by perm, then solve for a small weight change making degree(v) = D + eps*(v+1)
    exactly (least-norm solution; the incidence matrix of this non-bipartite graph has full rank)."""
    n, E = build(m, s, x)
    if perm is not None:
        E = [(int(perm[u]), int(perm[v]), w) for u, v, w in E]
    Bm = np.zeros((n, len(E)))
    for j, (u, v, _) in enumerate(E):
        Bm[u, j] = Bm[v, j] = 1
    target = np.array([eps * (v + 1) for v in range(n)])
    dw = np.linalg.lstsq(Bm, target, rcond=None)[0]
    return n, [(u, v, w + float(dw[j])) for j, (u, v, w) in enumerate(E)]


def check_perturbed(m=5, s=100, x=101, trials=3, seed=0):
    from cutlib import gomory_hu_tree, kapoor_F, tolerance
    rng = np.random.default_rng(seed)
    degs0 = None
    for t in range(trials):
        perm = rng.permutation(3 * m)
        n, E = perturbed(m, s, x, perm=perm)
        d = cut_table(n, E); tol = 1e-9
        deg = [round(float(d[1 << v]), 6) for v in range(n)]
        sizes = np.array([popcount(S) for S in range(1 << n)])
        nt = (sizes >= 2) & (sizes <= n - 2)
        W = partition_weights(n, E); opt = W.min(); idx = np.flatnonzero(W <= opt + tol)
        _, M = labelings(n)
        clusters = sorted(sum(1 << int(perm[v]) for v in range(c * m, (c + 1) * m)) for c in range(3))
        tree = gomory_hu_tree(n, d, tol)
        c = int(np.argmax(deg))
        star = all(c in (a, b) for a, b, _ in tree)
        print(f"perm {t}: degrees distinct {len(set(deg)) == n}, same as first {degs0 is None or deg == degs0}, "
              f"non-trivial cuts > max degree {d[nt].min() > max(deg) + tol}, unique optimum = clusters "
              f"{len(idx) == 1 and sorted(int(q) for q in M[idx[0]]) == clusters}, star tree at max degree {star}, "
              f"F(T) > OPT {kapoor_F(n, d, tree) > opt + tol}")
        degs0 = degs0 or deg
