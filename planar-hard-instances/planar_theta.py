"""Hard minimum 3-cuts of plane graphs via light thetas in the dual (exhaustive checks).

For a plane graph G with edge weights >= 1 and edge connectivity lambda:
  * a hard optimum (all pair weights < lambda) is dual to a theta in the dual H whose three
    strands each weigh < lambda, hence each has at most ell = ceil(lambda) - 1 edges;
  * OPT(G) = min(greedy(S), T*), where T* is the least weight of such a hop-bounded theta.
The second claim is what the linear-time algorithm (Baker layering + bounded-treewidth
dynamic programming) computes. Here T* is found by exhaustive bounded search, both over the
whole dual and inside Baker windows of consecutive BFS layers, and compared with the
brute-force optimum of G.
Usage: python3 planar_theta.py trials seed
"""
import itertools, sys
import numpy as np
import networkx as nx
from scipy.spatial import Delaunay
from cutlib import cut_table, optimum, edge_connectivity, global_min_cuts, greedy_value, labelings, \
    pair_weight


def random_plane_graph(n, rng, wmax, keep=0.8):
    while True:
        pts = rng.random((n, 2))
        E = set()
        for s in Delaunay(pts).simplices:
            for a, b in ((s[0], s[1]), (s[1], s[2]), (s[0], s[2])):
                E.add((min(a, b), max(a, b)))
        E = [e for e in E if rng.random() < keep]
        G = nx.Graph(); G.add_nodes_from(range(n)); G.add_edges_from(E)
        if nx.is_connected(G):
            pos = {i: pts[i] for i in range(n)}
            return G, pos, ({e: int(rng.integers(1, wmax + 1)) for e in G.edges()} if wmax > 0 else {e: float(rng.uniform(1, 3)) for e in G.edges()})


def dual(G, pos):
    """Dual multigraph: faces as vertices; one dual edge per primal edge."""
    emb = nx.PlanarEmbedding()
    for v in G.nodes():
        nbrs = sorted(G[v], key=lambda u: np.arctan2(pos[u][1] - pos[v][1], pos[u][0] - pos[v][0]))
        for i, u in enumerate(nbrs):
            if i == 0:
                emb.add_half_edge_first(v, u)
            else:
                emb.add_half_edge_ccw(v, u, nbrs[i - 1])
    emb.check_structure()
    face_of = {}
    faces = []
    for v, u in emb.edges():
        if (v, u) in face_of:
            continue
        f = emb.traverse_face(v, u, mark_half_edges=None)
        k = len(faces); faces.append(f)
        # mark half-edges of this face
        for a, b in zip(f, f[1:] + f[:1]):
            face_of[(a, b)] = k
    D = []
    for (a, b) in G.edges():
        D.append((face_of[(a, b)], face_of[(b, a)], (a, b)))
    return len(faces), D


def light_thetas_min(nf, D, w, lam, allowed=None):
    """Least weight of a theta in the dual with every strand of weight < lam (exhaustive).
    allowed: optional set of dual vertices the theta must stay inside."""
    adj = {f: [] for f in range(nf)}
    for idx, (a, b, e) in enumerate(D):
        if a == b:
            continue                      # loops (primal bridges) never lie on a theta
        adj[a].append((b, idx)); adj[b].append((a, idx))
    best = np.inf
    verts = range(nf) if allowed is None else sorted(allowed)
    for u in verts:
        # all simple paths from u with weight < lam, as (end, vertex set, edge set, weight)
        paths = {}
        stack = [(u, (u,), (), 0)]
        while stack:
            x, vs, es, wt = stack.pop()
            for y, idx in adj[x]:
                nw = wt + w[D[idx][2]]
                if nw >= lam or y in vs or (allowed is not None and y not in allowed):
                    continue
                if y > u:
                    paths.setdefault(y, []).append((frozenset(vs[1:]), frozenset(es + (idx,)), nw))
                stack.append((y, vs + (y,), es + (idx,), nw))
        for v, P in paths.items():
            P.sort(key=lambda p: p[2])
            k = len(P)
            for i in range(k):
                if 3 * P[i][2] >= best:
                    break
                for j in range(i + 1, k):
                    if P[i][2] + 2 * P[j][2] >= best:
                        break
                    if P[i][0] & P[j][0] or P[i][1] & P[j][1]:
                        continue
                    for l in range(j + 1, k):
                        tot = P[i][2] + P[j][2] + P[l][2]
                        if tot >= best:
                            break
                        if P[l][0] & (P[i][0] | P[j][0]) or P[l][1] & (P[i][1] | P[j][1]):
                            continue
                        # internal vertices must avoid v too: v is not in vs[1:] since paths end at v
                        best = tot
    return best


def baker_windows(nf, D, w, lam, ell):
    """T* computed window by window: BFS layers (by hops) in the dual from face 0, windows of
    2*Dh consecutive layers starting at multiples of Dh, Dh = ceil(3*ell/2) + 1."""
    H = nx.MultiGraph(); H.add_nodes_from(range(nf))
    for a, b, e in D:
        if a != b:
            H.add_edge(a, b)
    layer = nx.single_source_shortest_path_length(H, 0)
    Dh = (3 * ell + 1) // 2 + 1
    top = max(layer.values())
    best = np.inf
    for start in range(0, top + 1, Dh):
        allowed = {f for f, l in layer.items() if start <= l < start + 2 * Dh}
        best = min(best, light_thetas_min(nf, D, w, lam, allowed))
    return best


def main(trials=300, seed=1):
    rng = np.random.default_rng(seed)
    stats = dict(graphs=0, hard=0, ok=0, ok_windows=0, theta_wins=0, theta_below_opt=0)
    for t in range(trials):
        n = int(rng.integers(7, 12))
        G, pos, w = random_plane_graph(n, rng, wmax=int(rng.choice([1, 2, 3])), keep=float(rng.choice([0.8, 1.0])))
        E = [(a, b, float(w[(a, b)])) for a, b in G.edges()]
        d = cut_table(n, E)
        opt, idx, _ = optimum(n, E, 1e-9)
        lam, cuts = global_min_cuts(n, d, 1e-9)
        gr = greedy_value(n, d, cuts[0])
        _, M = labelings(n)
        hard = all(max(pair_weight(d, *pq) for pq in itertools.combinations(M[i], 2)) < lam - 1e-9 for i in idx)
        nf, Dd = dual(G, pos)
        ell = int(np.ceil(lam)) - 1
        T = light_thetas_min(nf, Dd, w, lam)
        Tw = baker_windows(nf, Dd, w, lam, ell)
        stats["graphs"] += 1
        stats["hard"] += hard
        stats["ok"] += abs(min(gr, T) - opt) < 1e-9
        stats["ok_windows"] += abs(min(gr, Tw) - opt) < 1e-9
        stats["theta_wins"] += T < gr - 1e-9
        stats["theta_below_opt"] += T < opt - 1e-9
    print(f"graphs {stats['graphs']}, all optima hard in {stats['hard']}, greedy inexact (theta strictly better) in "
          f"{stats['theta_wins']}; theta lighter than OPT (impossible) in {stats['theta_below_opt']}; OPT = min(greedy, T*) in {stats['ok']}; with Baker windows in {stats['ok_windows']}")
    ok = stats["ok"] == stats["graphs"] == stats["ok_windows"] and stats["theta_below_opt"] == 0
    print("RESULT:", "all checks passed" if ok else "MISMATCH")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main(*(int(a) for a in sys.argv[1:])))
