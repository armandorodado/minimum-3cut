"""Linear-programming search for a graph where single linkage + Gomory-Hu sides + singletons
miss every optimum.

Fix a random tree T with an admissible 3-colouring P (no part a side, no merge; bank.py),
and a random spanning tree M with an order of its edges, such that no single-linkage
cluster (union of components while adding M's edges in that order) is a part of P or the
complement of one. Constraints (linear in the weights):
  * M is the maximum spanning tree and its edges are strictly decreasing in the given order;
  * T is a Gomory-Hu tree;
  * P beats every other 3-partition by delta.
Maximize delta; re-check feasible solutions exhaustively.
Usage: python3 sl_lp.py n tries seed
"""
import itertools, json, sys
import numpy as np
import networkx as nx
from scipy.optimize import linprog
import bank as B
from cutlib import labelings, fundamental_side
from families import Inst, fam_sides, fam_singletons
from fam2 import fam_single_linkage

ETA = 1e-3


def main(n, tries, seed):
    rng = np.random.default_rng(seed)
    pairs = list(itertools.combinations(range(n), 2)); P = len(pairs)
    pid = {p: i for i, p in enumerate(pairs)}
    full = (1 << n) - 1
    cutrow = {}
    def cut(S):
        if S not in cutrow:
            r = np.zeros(P + 1)
            for (u, v), i in pid.items():
                if ((S >> u) & 1) != ((S >> v) & 1):
                    r[i] = 1
            cutrow[S] = r
        return cutrow[S]
    L, Mlab = labelings(n)
    found = []
    for t in range(tries):
        Tg = nx.random_labeled_tree(n, seed=int(rng.integers(1 << 30)))
        tree = [(int(a), int(b), 0) for a, b in Tg.edges()]
        cols = [c for c in B.valid_colourings(n, tree) if min(bin(p).count("1") for p in c) >= 2]
        if not cols:
            continue
        parts = list(cols[int(rng.integers(len(cols)))])
        bad = set(parts) | {full ^ p for p in parts}
        # random maximum spanning tree M and edge order avoiding bad clusters
        ok = False
        for _ in range(200):
            Mg = nx.random_labeled_tree(n, seed=int(rng.integers(1 << 30)))
            order = list(Mg.edges()); rng.shuffle(order)
            comp = {v: 1 << v for v in range(n)}; good = True
            for u, v in order:
                X = comp[u] | comp[v]
                if X in bad:
                    good = False; break
                for x in range(n):
                    if (X >> x) & 1:
                        comp[x] = X
            if good:
                ok = True; break
        if not ok:
            continue
        A, b = [], []
        e = lambda u, v: pid[(min(u, v), max(u, v))]
        for (u1, v1), (u2, v2) in zip(order, order[1:]):            # strictly decreasing
            r = np.zeros(P + 1); r[e(u2, v2)] = 1; r[e(u1, v1)] = -1
            A.append(r); b.append(-ETA)
        rank = {frozenset(ed): i for i, ed in enumerate(order)}
        for u, v in pairs:                                           # cycle property
            if frozenset((u, v)) in rank:
                continue
            path = nx.shortest_path(Mg, u, v)
            for a, c in zip(path, path[1:]):
                r = np.zeros(P + 1); r[e(u, v)] = 1; r[e(a, c)] = -1
                A.append(r); b.append(-ETA)
        for x, y, _ in tree:                                         # Gomory-Hu tree
            F = fundamental_side(n, tree, x, y)
            for S in range(1, full):
                if (S >> x) & 1 and not (S >> y) & 1 and S != F:
                    A.append(cut(F) - cut(S)); b.append(0.0)
        tgt = tuple(sorted(parts))
        W0 = (cut(parts[0]) + cut(parts[1]) + cut(parts[2])) / 2
        for row in Mlab:                                              # unique optimum
            q = tuple(sorted(int(x) for x in row))
            if q == tgt:
                continue
            r = W0 - (cut(q[0]) + cut(q[1]) + cut(q[2])) / 2; r[-1] = 1
            A.append(r); b.append(0.0)
        c = np.zeros(P + 1); c[-1] = -1
        res = linprog(c, A_ub=np.array(A), b_ub=b, A_eq=[np.append(np.ones(P), 0.0)], b_eq=[float(n)],
                      bounds=[(0, None)] * P + [(None, 1)], method="highs")
        if res.status == 0 and -res.fun > 1e-6:
            E = [(u, v, float(x)) for (u, v), x in zip(pairs, res.x[:-1]) if x > 1e-9]
            I = Inst(n, E)
            hit = I.hits(fam_single_linkage(I) | fam_sides(I) | fam_singletons(I))
            print(f"try {t}: LP delta {-res.fun:.4g}; SL+sides+singletons hits = {hit}", flush=True)
            found.append(dict(n=n, E=E, delta=-res.fun, hits=bool(hit)))
    print(f"n={n} seed={seed}: {len(found)} feasible; {sum(not f['hits'] for f in found)} counterexamples")
    json.dump(found, open(f"sl_lp_{n}_{seed}.json", "w"))


if __name__ == "__main__":
    main(*(int(a) for a in sys.argv[1:]))
