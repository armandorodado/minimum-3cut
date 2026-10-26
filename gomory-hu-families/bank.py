"""Bank of hard instances for testing candidate families.

Every instance is a dict {kind, n, E}. Kinds:
  lp      : optima of the Gomory-Hu linear program for random trees and 3-colourings
            (n = 7..9), perturbed, kept when F(T) > OPT (the tree's sides fail);
  cluster : noisy three-cluster graphs (n = 7..12) whose optima are all hard;
  random  : random planar/general graphs (n = 6..10) whose optima are all hard;
  struct  : near-complete / circulant / wheel / cluster graphs whose optima are all hard;
  thm9    : the instance of Theorem 9.
Saved to bank.json.
"""
import itertools, json, sys
import numpy as np
import networkx as nx
from scipy.optimize import linprog
from cutlib import (cut_table, tolerance, optimum, labelings, gomory_hu_tree, kapoor_F,
                    edge_connectivity, is_hard, fundamental_side, random_instance, structured,
                    to_instance)


def all_hard(n, E):
    d, tol = cut_table(n, E), tolerance(E)
    opt, idx, _ = optimum(n, E, tol)
    _, M = labelings(n)
    lam = edge_connectivity(n, d)
    return all(is_hard(d, M[i], lam, tol) for i in idx), d, tol, opt


def gh_fails(n, E):
    d, tol = cut_table(n, E), tolerance(E)
    opt, _, _ = optimum(n, E, tol)
    return kapoor_F(n, d, gomory_hu_tree(n, d, tol)) > opt + tol


# ------------------------------------------------------------------ LP family
def valid_colourings(n, tree):
    """3-partitions with no part a side of T and no non-trivial merge of a side (Lemma 7)."""
    full = (1 << n) - 1
    sides = []
    for x, y, _ in tree:
        F = fundamental_side(n, tree, x, y)
        sides += [(x, F), (y, full ^ F)]
    sideset = {F for _, F in sides}
    out = []
    for L in itertools.product(range(3), repeat=n - 1):
        lab = (0,) + L
        if 1 not in lab or 2 not in lab or lab.index(1) > lab.index(2):
            continue
        parts = [sum(1 << v for v in range(n) if lab[v] == k) for k in range(3)]
        if any(p in sideset for p in parts):
            continue
        ok = True
        for x, X in sides:
            P = parts[lab[x]]
            if X & P == X:
                continue
            if any(Q & X == Q for Q in parts if Q != P):
                continue
            ok = False; break
        if ok:
            out.append(tuple(parts))
    return out


def lp_instance(n, rng):
    T = nx.random_labeled_tree(n, seed=int(rng.integers(1 << 30))) if hasattr(nx, "random_labeled_tree") \
        else nx.random_tree(n, seed=int(rng.integers(1 << 30)))
    tree = [(int(a), int(b), 0) for a, b in T.edges()]
    cols = valid_colourings(n, tree)
    if not cols:
        return None
    parts = list(cols[int(rng.integers(len(cols)))])
    pairs = list(itertools.combinations(range(n), 2))
    P = len(pairs)
    full = (1 << n) - 1
    cutrow = lambda S: np.array([1.0 if ((S >> u) & 1) != ((S >> v) & 1) else 0.0 for u, v in pairs])
    rows = {}
    def row(S):
        if S not in rows:
            rows[S] = cutrow(S)
        return rows[S]
    A_ub, b_ub = [], []
    # Gomory-Hu: every cut separating x, y weighs at least the fundamental cut
    for x, y, _ in tree:
        F = fundamental_side(n, tree, x, y)
        rF = row(F)
        for S in range(1, full):
            if (S >> x) & 1 and not (S >> y) & 1 and S != F:
                A_ub.append(np.append(rF - row(S), 0.0)); b_ub.append(0.0)
    # every 3-partition with a side of T as a part is heavier than (A,B,C) by delta
    sides = set()
    for x, y, _ in tree:
        F = fundamental_side(n, tree, x, y); sides |= {F, full ^ F}
    if any(p in sides for p in parts):
        return None
    W0 = sum(row(p) for p in parts) / 2
    for X in sides:
        R = full ^ X
        if bin(R).count("1") < 2:
            continue
        rest = [v for v in range(n) if (R >> v) & 1]
        for k in range(1, 1 << (len(rest) - 1)):
            Y = sum(1 << rest[i] for i in range(len(rest)) if (k >> i) & 1)
            Z = R ^ Y
            Wp = (row(X) + row(Y) + row(Z)) / 2
            A_ub.append(np.append(W0 - Wp, 1.0)); b_ub.append(0.0)
    A_eq = [np.append(W0, 0.0)]; b_eq = [1.0]
    c = np.zeros(P + 1); c[-1] = -1; c[:-1] = rng.normal(0, 0.02, P)
    bounds = [(0, 1)] * P + [(None, 1)]
    r = linprog(c, A_ub=np.array(A_ub), b_ub=b_ub, A_eq=np.array(A_eq), b_eq=b_eq,
                bounds=bounds, method="highs")
    if r.status != 0 or -r.fun <= 1e-6:
        return None
    out = []
    for _ in range(4):
        E = [(u, v, float(x) * float(np.exp(rng.normal(0, rng.choice([0.01, 0.03, 0.08])))))
             for (u, v), x in zip(pairs, r.x[:-1]) if x > 1e-9]
        G = nx.Graph(); G.add_nodes_from(range(n)); G.add_edges_from((u, v) for u, v, _ in E)
        if nx.is_connected(G) and gh_fails(n, E):
            out.append(E)
    return out


# ------------------------------------------------------------------ cluster family
def cluster_instance(rng):
    sizes = rng.integers(2, 5, 3)
    n = int(sizes.sum())
    lab = np.repeat(np.arange(3), sizes); rng.shuffle(lab)
    m = sizes.mean()
    beta = rng.uniform(0.5, 1.2) / (2 * m)
    E = []
    for u, v in itertools.combinations(range(n), 2):
        if lab[u] == lab[v]:
            w = rng.uniform(0.6, 1.4)
        else:
            w = beta * rng.uniform(0.0, 2.0) if rng.random() < 0.8 else 0.0
        if w > 0:
            E.append((u, v, float(w)))
    G = nx.Graph(); G.add_nodes_from(range(n)); G.add_edges_from((u, v) for u, v, _ in E)
    return (n, E) if nx.is_connected(G) else None


def main(n_lp=120, n_cl=300, n_rand=3000, n_struct=200, seed=3):
    rng = np.random.default_rng(seed)
    bank = []
    # Theorem 9
    inst = json.load(open("theorem9_instance.json"))
    V = inst["vertices"]; ix = {v: i for i, v in enumerate(V)}
    bank.append(dict(kind="thm9", n=7, E=[(ix[a], ix[b], float(w)) for a, b, w in inst["edges"]]))
    # LP
    tries = got = 0
    while got < n_lp and tries < 3000:
        tries += 1
        n = int(rng.integers(7, 10))
        res = lp_instance(n, rng)
        for E in res or []:
            bank.append(dict(kind="lp", n=n, E=E)); got += 1
    print(f"lp: {got} instances with F(T) > OPT from {tries} tree/colouring tries", flush=True)
    # clusters
    got = 0
    for _ in range(n_cl):
        r = cluster_instance(rng)
        if r and all_hard(*r)[0]:
            bank.append(dict(kind="cluster", n=r[0], E=r[1])); got += 1
    print(f"cluster: {got}", flush=True)
    # random
    got = 0
    for t in range(n_rand):
        n, E = random_instance(t, rng, 6, 10)
        if all_hard(n, E)[0]:
            bank.append(dict(kind="random", n=n, E=E)); got += 1
    print(f"random: {got}", flush=True)
    got = 0
    for t in range(n_struct):
        kind = ["near-complete", "circulant", "clusters", "wheel"][t % 4]
        G = structured(kind, int(rng.integers(7, 11)), rng)
        if G is None:
            continue
        n, E = to_instance(G)
        if all_hard(n, E)[0]:
            bank.append(dict(kind="struct", n=n, E=E)); got += 1
    print(f"struct: {got}", flush=True)
    json.dump(bank, open("bank.json", "w"))
    fails = sum(gh_fails(b["n"], b["E"]) for b in bank)
    print(f"total {len(bank)}, F(T) > OPT in {fails}")


if __name__ == "__main__":
    main()
