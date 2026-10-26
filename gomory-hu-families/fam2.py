"""Cheap laminar families: single linkage (maximum spanning tree) and Stoer-Wagner supernodes."""
import json, sys
import numpy as np
import networkx as nx
from families import Inst, fam_sides, fam_singletons, fam_NI


def fam_single_linkage(I):
    """All clusters of the single-linkage hierarchy: components of the maximum spanning
    forest restricted to its heaviest edges, for every threshold."""
    G = nx.Graph(); G.add_nodes_from(range(I.n))
    for u, v, w in I.E:
        if G.has_edge(u, v):
            G[u][v]["weight"] += w
        else:
            G.add_edge(u, v, weight=w)
    T = nx.maximum_spanning_tree(G)
    edges = sorted(T.edges(data="weight"), key=lambda e: -e[2])
    comp = {v: 1 << v for v in range(I.n)}
    out = set(comp.values())
    for u, v, _ in edges:
        X = comp[u] | comp[v]
        for x in range(I.n):
            if (X >> x) & 1:
                comp[x] = X
        out.add(X)
    return out | {I.full ^ X for X in out}


def fam_stoer_wagner(I):
    """Supernodes formed during the Stoer-Wagner algorithm (maximum adjacency orderings)."""
    W = np.zeros((I.n, I.n))
    for u, v, w in I.E:
        W[u, v] += w; W[v, u] += w
    groups = {v: 1 << v for v in range(I.n)}
    out = set(groups.values())
    active = list(range(I.n))
    while len(active) > 1:
        a = [active[0]]
        rest = set(active[1:])
        conn = {v: W[active[0], v] for v in rest}
        while rest:
            z = max(rest, key=lambda v: (conn[v], -v))
            a.append(z); rest.remove(z)
            for v in rest:
                conn[v] += W[z, v]
        s, t = a[-2], a[-1]
        out.add(groups[t])                     # the cut of the phase
        groups[s] |= groups[t]; out.add(groups[s])
        W[s, :] += W[t, :]; W[:, s] += W[:, t]; W[s, s] = 0
        active.remove(t)
    return out | {I.full ^ X for X in out if X != I.full}


def main(path="bank.json"):
    bank = json.load(open(path))
    rows = {}
    for b in bank:
        I = Inst(b["n"], [tuple(e) for e in b["E"]])
        sd, sg = fam_sides(I), fam_singletons(I)
        sl, sw = fam_single_linkage(I), fam_stoer_wagner(I)
        res = {"single linkage": I.hits(sl), "single linkage+sides": I.hits(sl | sd),
               "Stoer-Wagner": I.hits(sw), "Stoer-Wagner+sides": I.hits(sw | sd | sg),
               "SL+SW+sides": I.hits(sl | sw | sd | sg)}
        for k, v in res.items():
            s = rows.setdefault(k, {}).setdefault(b["kind"], [0, 0]); s[0] += v; s[1] += 1
    kinds = sorted({b["kind"] for b in bank})
    print("family".ljust(26) + "".join(k.rjust(11) for k in kinds))
    for k, r in rows.items():
        print(k.ljust(26) + "".join(f"{r[kd][0]}/{r[kd][1]}".rjust(11) for kd in kinds))


if __name__ == "__main__":
    main(*sys.argv[1:])
