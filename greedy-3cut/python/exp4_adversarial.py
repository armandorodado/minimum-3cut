"""Adversarial weight search against F(T) = OPT.

Each climb starts from a random planar (Delaunay, edges kept w.p. 0.85) or general
(G(n, 0.45)) graph with 11-13 vertices and weights uniform in [1, 10], and hill-climbs
on the weights to maximise
    t = F(T) - OPT_nonGH,
where OPT_nonGH is the least weight of a 3-partition none of whose parts is a
Gomory-Hu side. t > 0 means F(T) > OPT. A step multiplies each weight, with
probability 0.3, by exp(N(0, 0.35)), clipped to [1e-3, 1e3], and is kept if t does
not decrease.

Usage: python3 exp4_adversarial.py [climbs_per_seed] [steps] [seeds ...]
Defaults: 60 climbs per seed, 300 steps, seeds 7 99 2026 31 (240 climbs).
Runtime: about 3 minutes per seed, 13 minutes in all, with the defaults.
"""
import sys, time
import numpy as np
import networkx as nx
from scipy.spatial import Delaunay
from cutlib import (cut_table, tolerance, labelings, partition_weights, gomory_hu_tree,
                    tree_sides)


def start_graph(n, planar, rng):
    while True:
        if planar:
            pts = rng.random((n, 2))
            E = set()
            for s in Delaunay(pts).simplices:
                for a, b in ((s[0], s[1]), (s[1], s[2]), (s[0], s[2])):
                    E.add((int(min(a, b)), int(max(a, b))))
            E = [e for e in sorted(E) if rng.random() < 0.85]
        else:
            E = [(u, v) for u in range(n) for v in range(u + 1, n) if rng.random() < 0.45]
        G = nx.Graph(); G.add_nodes_from(range(n)); G.add_edges_from(E)
        if nx.is_connected(G):
            return E


def score(n, pairs, w):
    E = [(u, v, x) for (u, v), x in zip(pairs, w)]
    d, tol = cut_table(n, E), tolerance(E)
    _, M = labelings(n)
    W = partition_weights(n, E)
    tree = gomory_hu_tree(n, d, tol)
    side = np.zeros(1 << n, bool)
    for X in tree_sides(n, tree):
        side[X] = True
    has = side[M[:, 0]] | side[M[:, 1]] | side[M[:, 2]]
    F = W[has].min() if has.any() else np.inf
    rest = W[~has].min() if (~has).any() else np.inf
    return F - rest, F, tol


def main(climbs=60, steps=300, seeds=(7, 99, 2026, 31)):
    t0 = time.time()
    best_rel, found, total = -np.inf, 0, 0
    for seed in seeds:
        rng = np.random.default_rng(seed)
        for c in range(climbs):
            n = int(rng.integers(11, 14))
            pairs = start_graph(n, c % 2 == 0, rng)
            w = rng.uniform(1, 10, len(pairs))
            t, F, tol = score(n, pairs, w)
            for _ in range(steps):
                mask = rng.random(len(w)) < 0.3
                w2 = np.clip(w * np.exp(rng.normal(0, 0.35, len(w)) * mask), 1e-3, 1e3)
                t2, F2, tol2 = score(n, pairs, w2)
                if t2 >= t - tol2:
                    w, t, F, tol = w2, t2, F2, tol2
                if t > tol:
                    break
            total += 1
            best_rel = max(best_rel, t / F)
            if t > tol:
                found += 1
                print(f"seed {seed} climb {c}: F(T) > OPT, n={n}, edges={pairs}, weights={list(w)}")
        print(f"seed {seed}: done, {total} climbs so far, best relative t {best_rel:.4f}, "
              f"{time.time() - t0:.0f} s", flush=True)
    print(f"climbs {total}, climbs reaching F(T) > OPT {found}, best relative t {best_rel:.4f}")
    print("RESULT:", f"{found} of {total} climbs found F(T) > OPT")
    return 0


if __name__ == "__main__":
    a = sys.argv[1:]
    main(int(a[0]) if a else 60, int(a[1]) if len(a) > 1 else 300,
         tuple(int(x) for x in a[2:]) or (7, 99, 2026, 31))
