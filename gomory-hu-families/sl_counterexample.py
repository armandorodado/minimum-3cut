"""A counterexample to the single-linkage family (with Gomory-Hu sides and singletons).

Graph: three clusters A, B, C of size m (inner weight 1, inter-cluster weight beta), plus two
heavy inter-cluster edges a1-b1 and b2-c1 of weight h > 1 (replacing beta on those pairs).
Single linkage merges a1 with b1 and b2 with c1 before any weight-1 edge, so no cluster
and no complement of a cluster is ever a single-linkage component.

Exact check (integer arithmetic, weights scaled by q; beta = p/q, h = hq/q), using the
symmetry of the generic vertices: a vertex set / 3-partition is described by where the four
special vertices a1, b1, b2, c1 go and by how many generic vertices of each cluster go where.
Checks:
  (1) every cut with >= 2 vertices on each side is heavier than every vertex degree
      (so, after a tiny per-vertex perturbation, the unique Gomory-Hu tree is a star whose
      sides are singletons and their complements);
  (2) the clusters are the unique minimum-weight 3-partition, and they are hard.
Then builds the graph explicitly (with a tiny perturbation 1e-6*(u+v)) and confirms that single
linkage + singletons + their complements contains no cluster or complement.
Usage: python3 sl_counterexample.py m p q hq
"""
import itertools, sys
import numpy as np
import networkx as nx

SPEC = ["a1", "b1", "b2", "c1"]
CL = {"a1": 0, "b1": 1, "b2": 1, "c1": 2}


def weights(p, q, hq):
    def w(x, y):          # x, y: special names or ("g", cluster)
        cx = CL[x] if x in CL else x[1]
        cy = CL[y] if y in CL else y[1]
        if {x, y} in ({"a1", "b1"}, {"b2", "c1"}):
            return hq
        return q if cx == cy else p
    return w


def main(m, p, q, hq):
    w = weights(p, q, hq)
    G = [m - 1, m - 2, m - 1]                       # generic vertices per cluster
    n = 3 * m
    # degrees
    def deg(v):
        tot = 0
        for c in range(3):
            tot += (G[c] - (0 if (v in CL or c != v[1]) else 1)) * w(v, ("g", c))
        for s in SPEC:
            if s != v:
                tot += w(v, s)
        return tot
    degs = [deg(s) for s in SPEC] + [deg(("g", c)) for c in range(3)]
    Dmax = max(degs)
    # (1) cuts
    ok1 = True; min_nt = None
    for sp in itertools.product([0, 1], repeat=4):
        for u in itertools.product(*(range(g + 1) for g in G)):
            size = sum(sp) + sum(u)
            if not 2 <= size <= n - 2:
                continue
            d = 0
            ins = [s for s, b in zip(SPEC, sp) if b]; outs = [s for s, b in zip(SPEC, sp) if not b]
            d += sum(w(x, y) for x in ins for y in outs)
            for c in range(3):
                for s in ins:
                    d += (G[c] - u[c]) * w(s, ("g", c))
                for s in outs:
                    d += u[c] * w(s, ("g", c))
                for c2 in range(3):
                    d += u[c] * (G[c2] - u[c2]) * w(("g", c), ("g", c2))
            ok1 &= d > Dmax
            min_nt = d if min_nt is None else min(min_nt, d)
    # (2) 3-partitions
    def comps3(g):
        return [(a, b, g - a - b) for a in range(g + 1) for b in range(g + 1 - a)]
    best = None; cnt = 0; target = None
    C3 = [comps3(g) for g in G]
    for lab in itertools.product(range(3), repeat=4):
        for cols in itertools.product(*C3):
            sizes = [sum(1 for l in lab if l == r) + sum(cols[c][r] for c in range(3)) for r in range(3)]
            if min(sizes) == 0:
                continue
            W = 0
            for (i, x), (j, y) in itertools.combinations(list(enumerate(SPEC)), 2):
                if lab[i] != lab[j]:
                    W += w(x, y)
            for i, s in enumerate(SPEC):
                for c in range(3):
                    W += (G[c] - cols[c][lab[i]]) * w(s, ("g", c))
            for c in range(3):
                for c2 in range(c, 3):
                    for r in range(3):
                        for r2 in range(3):
                            if r == r2:
                                continue
                            if c == c2 and r2 < r:
                                continue
                            W += cols[c][r] * cols[c2][r2] * w(("g", c), ("g", c2))
            # canonical "clusters" partition: labels equal cluster index, generics on the diagonal
            is_cl = all(lab[i] == CL[s] for i, s in enumerate(SPEC)) and \
                all(cols[c][r] == (G[c] if r == c else 0) for c in range(3) for r in range(3))
            if is_cl:
                target = W
            if best is None or W < best:
                best, cnt = W, 1
            elif W == best:
                cnt += 1
    # the clusters appear 3! = 6 times (labelled parts)
    ok2 = best == target and cnt == 6
    pairAB = m * m * p - p + hq                    # a1-b1 replaced beta by h
    pairBC = m * m * p - p + hq
    pairAC = m * m * p
    lam = min(degs)
    hard = max(pairAB, pairBC, pairAC) < lam
    # (3) explicit graph and single linkage
    names = []
    for c, cl in enumerate("abc"):
        names += [f"{cl}{i}" for i in range(1, m + 1)]
    idx = {v: i for i, v in enumerate(names)}
    clus = [set(range(c * m, (c + 1) * m)) for c in range(3)]
    Gx = nx.Graph()
    for u, v in itertools.combinations(range(n), 2):
        cu, cv = u // m, v // m
        wt = (q if cu == cv else p) + 1e-6 * (u + v)
        Gx.add_edge(u, v, weight=wt)
    for x, y in (("a1", "b1"), ("b2", "c1")):
        Gx[idx[x]][idx[y]]["weight"] = hq + 1e-6 * (idx[x] + idx[y])
    T = nx.maximum_spanning_tree(Gx)
    comp = {v: frozenset([v]) for v in range(n)}; fam = set(comp.values())
    for u, v, _ in sorted(T.edges(data="weight"), key=lambda e: -e[2]):
        X = comp[u] | comp[v]
        for z in X:
            comp[z] = X
        fam.add(X)
    allv = frozenset(range(n))
    fam |= {allv - X for X in fam}
    sl_hits = any(frozenset(c) in fam or (allv - frozenset(c)) in fam for c in clus)
    print(f"m={m} beta={p}/{q} h={hq}/{q}: non-trivial cuts > max degree {ok1} "
          f"(min non-trivial {min_nt} vs max degree {Dmax}); clusters unique optimum {ok2} "
          f"(OPT {target}); hard {hard}; single linkage+singletons+complements contains a cluster: {sl_hits}")
    return ok1 and ok2 and hard and not sl_hits


if __name__ == "__main__":
    print("RESULT:", "counterexample confirmed" if main(*(int(a) for a in sys.argv[1:])) else "not confirmed")
