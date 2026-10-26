"""Linear-programming search for a graph on which Stoer-Wagner supernodes miss every optimum.

Pick a target 3-partition P and a random Stoer-Wagner run (one maximum-adjacency ordering
per phase, start vertex = the first active supernode, as in fam2.fam_stoer_wagner) whose
supernodes never equal a part of P or the complement of one. The run is valid for weights w
iff every ordering is a strict maximum-adjacency ordering, which is a set of linear
inequalities in w. Add: P beats every other 3-partition by delta, and P is hard
(each pair weight <= every cut - delta). Maximize delta. delta > 0 gives a counterexample,
which is then re-checked exhaustively with the real implementation.
Usage: python3 sw_lp.py n tries seed
"""
import itertools, json, sys
import numpy as np
from scipy.optimize import linprog
from cutlib import labelings
from families import Inst, fam_singletons
from fam2 import fam_stoer_wagner

ETA = 1e-3


def random_run(n, parts, rng):
    full = (1 << n) - 1
    bad = set(parts) | {full ^ p for p in parts}
    groups = [1 << v for v in range(n)]          # active supernodes, in index order
    phases = []
    while len(groups) > 1:
        k = len(groups)
        for _ in range(200):
            perm = [0] + list(rng.permutation(np.arange(1, k)))
            s, t = perm[-2], perm[-1]
            merged = groups[s] | groups[t]
            if merged not in bad:
                break
        else:
            return None
        phases.append([groups[i] for i in perm])
        # stoer-wagner keeps s, absorbs t; the order of the active list is preserved
        groups = [g if i != s else merged for i, g in enumerate(groups) if i != t]
    return phases


def solve(n, parts, phases, hard=True, tree=None):
    pairs = list(itertools.combinations(range(n), 2))
    P = len(pairs); pid = {p: i for i, p in enumerate(pairs)}
    nv = P + 1                                   # weights, delta
    def conn(X, Y):
        r = np.zeros(nv)
        for u in range(n):
            if (X >> u) & 1:
                for v in range(n):
                    if (Y >> v) & 1:
                        r[pid[(min(u, v), max(u, v))]] += 1
        return r
    def cut(S):
        r = np.zeros(nv)
        for (u, v), i in pid.items():
            if ((S >> u) & 1) != ((S >> v) & 1):
                r[i] = 1
        return r
    A, b = [], []
    # strict maximum-adjacency orderings
    for order in phases:
        S = order[0]
        for i in range(1, len(order) - 1):
            nxt = order[i]
            cn = conn(S, nxt)
            for u in order[i + 1:]:
                A.append(conn(S, u) - cn); b.append(-ETA)
            S |= nxt
    # target beats every other 3-partition by delta
    L, M = labelings(n)
    tgt = tuple(sorted(parts))
    W0 = (cut(parts[0]) + cut(parts[1]) + cut(parts[2])) / 2
    cuts = {}
    def cutc(S):
        if S not in cuts:
            cuts[S] = cut(S)
        return cuts[S]
    for row in M:
        q = tuple(sorted(int(x) for x in row))
        if q == tgt:
            continue
        Wq = (cutc(q[0]) + cutc(q[1]) + cutc(q[2])) / 2
        r = W0 - Wq; r[-1] = 1
        A.append(r); b.append(0.0)
    # hardness: each pair weight <= every cut - delta
    full = (1 << n) - 1
    for X, Y in (itertools.combinations(parts, 2) if hard else []):
        cXY = conn(X, Y)
        for S in range(1, 1 << (n - 1)):
            r = cXY - cutc(S); r[-1] = 1
            A.append(r); b.append(0.0)
    if tree is not None:                         # T is a Gomory-Hu tree
        from cutlib import fundamental_side
        fullm = (1 << n) - 1
        for x, y, _ in tree:
            F = fundamental_side(n, tree, x, y)
            for S in range(1, fullm):
                if (S >> x) & 1 and not (S >> y) & 1 and S != F:
                    A.append(cutc(F) - cutc(S)); b.append(0.0)
    c = np.zeros(nv); c[-1] = -1
    Aeq = [np.append(np.ones(P), 0.0)]; beq = [float(n)]
    res = linprog(c, A_ub=np.array(A), b_ub=b, A_eq=np.array(Aeq), b_eq=beq,
                  bounds=[(0, None)] * P + [(None, 1)], method="highs")
    return res, pairs


def main(n, tries, seed, hard=1, withtree=0):
    rng = np.random.default_rng(seed)
    found = []
    for t in range(tries):
        tree = None
        if withtree:
            import networkx as nx, bank as B
            Tg = nx.random_labeled_tree(n, seed=int(rng.integers(1 << 30)))
            tree = [(int(a), int(b), 0) for a, b in Tg.edges()]
            cols = [c for c in B.valid_colourings(n, tree) if min(bin(p).count("1") for p in c) >= 2]
            if not cols:
                continue
            parts = list(cols[int(rng.integers(len(cols)))])
        else:
            lab = rng.integers(0, 3, n)
            if min(np.bincount(lab, minlength=3)) < 2:
                continue
            parts = [sum(1 << v for v in range(n) if lab[v] == k) for k in range(3)]
        phases = random_run(n, parts, rng)
        if phases is None:
            continue
        res, pairs = solve(n, parts, phases, bool(hard), tree)
        if res.status == 0 and -res.fun > 1e-6:
            E = [(u, v, float(x)) for (u, v), x in zip(pairs, res.x[:-1]) if x > 1e-9]
            I = Inst(n, E)
            from families import fam_sides
            fam = fam_stoer_wagner(I) | fam_singletons(I) | fam_sides(I)
            hit = I.hits(fam)
            print(f"try {t}: LP delta {-res.fun:.4g}; exhaustive check: SW hits = {hit}, "
                  f"optima {len(I.optima)}", flush=True)
            found.append(dict(n=n, E=E, delta=-res.fun, sw_hits=bool(hit)))
    print(f"n={n} seed={seed}: {len(found)} LP-feasible runs; "
          f"{sum(not f['sw_hits'] for f in found)} confirmed counterexamples")
    json.dump(found, open(f"sw_lp_{n}_{seed}_{hard}_{withtree}.json", "w"))


if __name__ == "__main__":
    main(*(int(a) for a in sys.argv[1:]))
