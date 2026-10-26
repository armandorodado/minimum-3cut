"""Structure of optimal light thetas in plane duals (Phase-0 hypothesis tests).
For hard instances (T* = OPT < greedy or all optima hard), record the optimal theta and test:
 H2a every strand is a shortest u-v path in H;  H2b the lightest strand is;
 H1 the lightest cycle of the theta is isometric;  H1' all three cycles are isometric;
 H3 the theta lies in SPT(u) plus at most 2 non-tree edges (for its branch vertex u or v).
"""
import itertools, sys
import numpy as np, networkx as nx
from planar_theta import random_plane_graph, dual
from cutlib import cut_table, optimum, global_min_cuts, greedy_value

def best_theta(nf, D, w, lam):
    adj = {f: [] for f in range(nf)}
    for idx, (a, b, e) in enumerate(D):
        if a != b:
            adj[a].append((b, idx)); adj[b].append((a, idx))
    best = (np.inf, None)
    for u in range(nf):
        paths = {}
        stack = [(u, (u,), (), 0)]
        while stack:
            x, vs, es, wt = stack.pop()
            for y, idx in adj[x]:
                nw = wt + w[D[idx][2]]
                if nw >= lam or y in vs: continue
                if y > u: paths.setdefault(y, []).append((vs + (y,), es + (idx,), nw))
                stack.append((y, vs + (y,), es + (idx,), nw))
        for v, P in paths.items():
            for a, b, c in itertools.combinations(P, 3):
                ia, ib, ic = set(a[0][1:-1]), set(b[0][1:-1]), set(c[0][1:-1])
                if ia & ib or ia & ic or ib & ic: continue
                if set(a[1]) & set(b[1]) or set(a[1]) & set(c[1]) or set(b[1]) & set(c[1]): continue
                t = a[2] + b[2] + c[2]
                if t < best[0]: best = (t, (u, v, [a, b, c]))
    return best

def main(trials=400, seed=5):
    rng = np.random.default_rng(seed)
    cnt = dict(n=0, h2a=0, h2b=0, h1=0, h1all=0, h3=0, h3all=0, h3all3=0)
    for t in range(trials):
        n = int(rng.integers(7, 12))
        G, pos, w = random_plane_graph(n, rng, wmax=int(sys.argv[3]) if len(sys.argv) > 3 else int(rng.choice([1, 2, 3])), keep=float(rng.choice([0.8, 1.0])))
        E = [(a, b, float(w[(a, b)])) for a, b in G.edges()]
        d = cut_table(n, E); opt, idx, _ = optimum(n, E, 1e-9)
        lam, cuts = global_min_cuts(n, d, 1e-9); gr = greedy_value(n, d, cuts[0])
        nf, D = dual(G, pos)
        T, th = best_theta(nf, D, w, lam)
        if th is None or abs(T - opt) > 1e-9: continue       # only instances where a light theta is optimal
        u, v, P = th
        H = nx.MultiGraph(); H.add_nodes_from(range(nf))
        for a, b, e in D:
            if a != b: H.add_edge(a, b, weight=w[e])
        dist = dict(nx.all_pairs_dijkstra_path_length(H, weight="weight"))
        cnt["n"] += 1
        wts = sorted(p[2] for p in P)
        cnt["h2a"] += all(abs(p[2] - dist[u][v]) < 1e-9 for p in P)
        cnt["h2b"] += abs(wts[0] - dist[u][v]) < 1e-9
        def isometric(p, q):
            cyc = list(p[0]) + list(reversed(q[0]))[1:-1]
            ew = [p[2], q[2]]
            # cumulative positions along the cycle
            pos_ = {}; acc = 0; seq = []
            for i, x in enumerate(p[0]):
                if i: acc += w[D[p[1][i-1]][2]]
                seq.append((x, acc))
            back = list(reversed(q[0])); qe = list(reversed(q[1])); acc2 = p[2]
            for i, x in enumerate(back[1:-1]):
                acc2 += w[D[qe[i]][2]]; seq.append((x, acc2))
            L = p[2] + q[2]
            for (x, ax), (y, ay) in itertools.combinations(seq, 2):
                arc = abs(ax - ay); 
                if min(arc, L - arc) > dist[x][y] + 1e-9: return False
            return True
        cyc = [(P[i], P[j]) for i, j in ((0, 1), (0, 2), (1, 2))]
        cw = [p[2] + q[2] for p, q in cyc]
        cnt["h1"] += isometric(*cyc[int(np.argmin(cw))])
        cnt["h1all"] += all(isometric(p, q) for p, q in cyc)
        # H3: theta edges minus SPT(u) edges (or SPT(v)) has at most 2 edges
        ok3 = False
        for r in (u, v):
            T_ = nx.minimum_spanning_tree(nx.Graph())  # placeholder
            _, paths_r = nx.single_source_dijkstra(H, r, weight="weight")
            tree_edges = set()
            for x, pth in paths_r.items():
                for a_, b_ in zip(pth, pth[1:]): tree_edges.add(frozenset((a_, b_)))
            th_edges = [frozenset((D[i][0], D[i][1])) for p in P for i in p[1]]
            ok3 |= sum(e not in tree_edges for e in th_edges) <= 2
        cnt["h3"] += ok3
        th_edges = [frozenset((D[i][0], D[i][1])) for p in P for i in p[1]]
        verts = set(x for p in P for x in p[0])
        worst = 0
        for z in verts:
            _, paths_z = nx.single_source_dijkstra(H, z, weight="weight")
            te = set()
            for x, pth in paths_z.items():
                for a_, b_ in zip(pth, pth[1:]): te.add(frozenset((a_, b_)))
            worst = max(worst, sum(e not in te for e in th_edges))
        cnt["h3all"] += worst <= 2
        cnt["h3all3"] += worst <= 3
    print(f"optimal light thetas examined {cnt['n']}: every strand shortest {cnt['h2a']}; lightest strand shortest {cnt['h2b']}; "
          f"lightest cycle isometric {cnt['h1']}; all cycles isometric {cnt['h1all']}; within SPT(branch)+2 edges {cnt['h3']}; within SPT(z)+2 edges for EVERY theta vertex z {cnt['h3all']} (+3 edges: {cnt['h3all3']})")

if __name__ == "__main__":
    main(*(int(a) for a in sys.argv[1:3]))
