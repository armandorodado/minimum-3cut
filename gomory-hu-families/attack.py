"""Hill-climb edge weights to find a graph where a candidate family misses every optimum.

Usage: python3 attack.py FAMILY [climbs] [steps] [seed]
FAMILY in: SL, SW, pairin, pairsep, NI, nontriv
Objective: gap = (val(family + sides + singletons) - OPT) / OPT; gap > 1e-9 is a failure.
"""
import json, sys, time
import numpy as np
import networkx as nx
from families import (Inst, fam_sides, fam_singletons, fam_NI, fam_nontriv_pair_in,
                      fam_nontriv_pair_sep, fam_nontriv_vertex)
from fam2 import fam_single_linkage, fam_stoer_wagner

FAM = {"SL": fam_single_linkage, "SW": fam_stoer_wagner, "pairin": fam_nontriv_pair_in,
       "pairsep": fam_nontriv_pair_sep, "NI": fam_NI, "nontriv": fam_nontriv_vertex}


from cutlib import labelings, partition_weights


def gap(n, E, fam):
    """(best 3-partition with a part in the family) - (best 3-partition with none), / OPT."""
    I = Inst(n, E)
    f = FAM[fam](I) | fam_singletons(I) | fam_sides(I)
    _, M = labelings(n)
    W = partition_weights(n, E)
    inf = np.isin(M, np.array(sorted(f), dtype=np.int64)).any(1)
    if inf.all():
        return -1.0
    return (W[inf].min() - W[~inf].min()) / I.opt


def start(n, rng):
    while True:
        G = nx.gnp_random_graph(n, rng.uniform(0.4, 0.9), seed=int(rng.integers(1 << 30)))
        if nx.is_connected(G):
            return [(u, v, float(rng.uniform(1, 10))) for u, v in G.edges()]


def main(fam, climbs=30, steps=200, seed=1):
    rng = np.random.default_rng(seed)
    found = []
    best_all = -1
    t0 = time.time()
    for c in range(climbs):
        n = int(rng.integers(7, 10))
        E = start(n, rng)
        g = gap(n, E, fam)
        for s in range(steps):
            E2 = [(u, v, float(np.clip(w * np.exp(rng.normal(0, 0.4)), 1e-3, 1e3))
                   if rng.random() < 0.3 else w) for u, v, w in E]
            g2 = gap(n, E2, fam)
            if g2 >= g:
                E, g = E2, g2
            if g > 1e-9:
                break
        best_all = max(best_all, g)
        if g > 1e-9:
            found.append(dict(n=n, E=E, gap=g))
            print(f"climb {c}: FAILURE n={n} gap {g:.4g}", flush=True)
    print(f"{fam}: {len(found)} failures in {climbs} climbs; best gap {best_all:.4g}; {time.time()-t0:.0f} s")
    json.dump(found, open(f"attack_{fam}_{seed}.json", "w"))


if __name__ == "__main__":
    a = sys.argv[1:]
    main(a[0], *(int(x) for x in a[1:]))
