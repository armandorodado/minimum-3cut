"""The caterpillar linear program of Section 5, and perturbations of its optima.

Part 1. For a fixed caterpillar tree shape T (B = |B| leaves at s, a spine of A-vertices,
C = |C| leaves at the end), the weights of all vertex pairs are variables, and the LP
imposes:
  * T is a Gomory-Hu cut tree (every cut separating the ends of a tree edge weighs at
    least that edge's fundamental cut);
  * (A, B, C) is optimal and hard (each pair weight <= every cut - 0.001);
  * OPT = 1;
and maximises the margin delta by which every 3-partition having a side of T as a part
is heavier than (A, B, C). delta > 0 means F(T) > OPT is possible for that shape.

Part 2. Each LP optimum with delta > 0 is perturbed 12 times (weights multiplied by
exp(N(0, 0.05))); for each perturbed graph we compare F(T), for its actual Gomory-Hu
tree, with OPT, and whether also trying as a part the set of leaf neighbours of each
tree vertex closes the gap (open question 1 of the paper).
Runtime: a few seconds.
"""
import itertools, sys, time
import numpy as np
import networkx as nx
from scipy.optimize import linprog
from cutlib import cut_table, tolerance, optimum, gomory_hu_tree, kapoor_F, induced_lambda


def build(k, p, m=0, aleaf_s=0, aleaf_u=0):
    T = nx.Graph(); part = {}
    spine = ["s"] + [f"u{i}" for i in range(m + 1)]
    for a, b in zip(spine, spine[1:]):
        T.add_edge(a, b)
    for v in spine:
        part[v] = "A"
    for i in range(k):
        T.add_edge("s", f"l{i}"); part[f"l{i}"] = "B"
    for j in range(p):
        T.add_edge(spine[-1], f"c{j}"); part[f"c{j}"] = "C"
    for i in range(aleaf_s):
        T.add_edge("s", f"as{i}"); part[f"as{i}"] = "A"
    for i in range(aleaf_u):
        T.add_edge(spine[1], f"au{i}"); part[f"au{i}"] = "A"
    return T, part


def solve(k, p, m=0, aleaf_s=0, aleaf_u=0, eps=1e-3):
    T, part = build(k, p, m, aleaf_s, aleaf_u)
    V = list(T.nodes()); n = len(V)
    pairs = list(itertools.combinations(V, 2)); idx = {pq: i for i, pq in enumerate(pairs)}
    nv = len(pairs) + 1; D = nv - 1

    def cutv(Y):
        c = np.zeros(nv)
        for (u, v), i in idx.items():
            if (u in Y) != (v in Y):
                c[i] += 1
        return c
    subsets = [frozenset(Y) for r in range(1, n) for Y in itertools.combinations(V, r)]
    ub, b, sides = [], [], set()
    for x, y in T.edges():
        T2 = T.copy(); T2.remove_edge(x, y)
        F = frozenset(nx.node_connected_component(T2, x)); sides |= {F, frozenset(V) - F}
        dF = cutv(F)
        for Y in subsets:
            if (x in Y) != (y in Y):
                ub.append(dF - cutv(Y)); b.append(0.0)
    labs = []
    for lab in itertools.product(range(3), repeat=n - 1):
        lab = (0,) + lab
        if 1 not in lab or 2 not in lab or lab.index(1) > lab.index(2):
            continue
        labs.append(dict(zip(V, lab)))

    def wpart(L):
        c = np.zeros(nv)
        for (u, v), i in idx.items():
            if L[u] != L[v]:
                c[i] += 1
        return c
    OPT = wpart({v: {"A": 0, "B": 1, "C": 2}[part[v]] for v in V})

    def pairw(P, Q):
        c = np.zeros(nv)
        for (u, v), i in idx.items():
            if {part[u], part[v]} == {P, Q}:
                c[i] += 1
        return c
    for P, Q in (("A", "B"), ("A", "C"), ("B", "C")):
        for Y in subsets:
            ub.append(pairw(P, Q) - cutv(Y)); b.append(-eps)
    for L in labs:
        Wl = wpart(L); ub.append(OPT - Wl); b.append(0.0)
        if any(frozenset(v for v in V if L[v] == i) in sides for i in range(3)):
            row = OPT - Wl; row[D] = 1; ub.append(row); b.append(0.0)
    obj = np.zeros(nv); obj[D] = -1
    r = linprog(obj, A_ub=np.array(ub), b_ub=np.array(b), A_eq=np.array([OPT]), b_eq=[1.0],
                bounds=[(0, None)] * (nv - 1) + [(None, 1)], method="highs")
    return r, V, pairs


def leaf_sets_value(n, d, tree, F):
    """min(F, best 3-cut with a part equal to the set of leaf neighbours of a tree vertex)."""
    T = nx.Graph(); T.add_edges_from((a, b) for a, b, _ in tree)
    full, best = (1 << n) - 1, F
    for v in T:
        X = sum(1 << u for u in T[v] if T.degree(u) == 1)
        if X and bin(full ^ X).count("1") >= 2:
            best = min(best, float(d[X]) + induced_lambda(d, full ^ X))
    return best


def main():
    t0 = time.time()
    shapes = [(1, 1), (1, 2), (2, 1), (2, 2), (3, 1), (2, 1, 1), (2, 2, 1), (2, 1, 0, 1),
              (2, 1, 0, 0, 1), (3, 2), (3, 3), (4, 2), (3, 2, 0, 1), (3, 2, 1), (3, 2, 0, 0, 1)]
    print("Part 1: LP margins (|B|, |C|, spine extra, extra A-leaves at s, extra A-leaves at u0)")
    positive = []
    for cfg in shapes:
        r, V, pairs = solve(*cfg)
        if r.status != 0:
            print(f"  shape {cfg}: LP status {r.status} ({r.message})")
            continue
        delta = -r.fun
        print(f"  shape {cfg}: max margin {delta:+.5f}")
        if delta > 1e-6:
            positive.append((cfg, r, V, pairs))
    print("Part 2: perturbed LP optima")
    rng = np.random.default_rng(12)
    graphs = fails = fixed = 0
    tree = None
    for cfg, r, V, pairs in positive:
        if len(V) > 10:
            continue
        ix = {v: i for i, v in enumerate(V)}
        for _ in range(12):
            E = [(ix[u], ix[v], float(x) * float(np.exp(rng.normal(0, 0.05))))
                 for (u, v), x in zip(pairs, r.x[:-1]) if x > 1e-12]
            G = nx.Graph(); G.add_nodes_from(range(len(V))); G.add_edges_from((u, v) for u, v, _ in E)
            if not nx.is_connected(G):
                continue
            n = len(V); d, tol = cut_table(n, E), tolerance(E)
            opt, _, _ = optimum(n, E, tol)
            tree = gomory_hu_tree(n, d, tol)
            F = kapoor_F(n, d, tree)
            graphs += 1
            if F > opt + tol:
                fails += 1
                fixed += leaf_sets_value(n, d, tree, F) <= opt + tol
    print(f"  perturbed graphs {graphs}, F(T) > OPT in {fails}")
    print(f"  adding the leaf-neighbour sets of tree vertices (open question 1) fixes {fixed} of {fails}")
    print(f"time {time.time() - t0:.0f} s")
    print("RESULT:", f"{len(positive)} shapes with positive margin; F(T) > OPT in {fails} of {graphs} perturbed graphs")
    return 0


if __name__ == "__main__":
    sys.exit(main())
