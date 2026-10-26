import sys; sys.path.insert(0,'.')
import numpy as np, networkx as nx
import planar_wheels as pw
from planar_theta import light_thetas_min
from cutlib import cut_table, optimum, global_min_cuts, greedy_value
n, E = pw.build(5, 100, 101)
G = nx.Graph(); G.add_weighted_edges_from(E)
ok, emb = nx.check_planarity(G)
face_of = {}; nf = 0
for v, u in emb.edges():
    if (v, u) in face_of: continue
    f = emb.traverse_face(v, u)
    for a, b in zip(f, f[1:] + f[:1]): face_of[(a, b)] = nf
    nf += 1
D = [(face_of[(a, b)], face_of[(b, a)], (a, b)) for a, b in G.edges()]
w = {(a, b): G[a][b]['weight'] for a, b in G.edges()}
d = cut_table(n, E); opt, idx, _ = optimum(n, E, 1e-9)
lam, cuts = global_min_cuts(n, d, 1e-9); gr = greedy_value(n, d, cuts[0])
T = light_thetas_min(nf, D, w, lam)
print(f"wheel ring n={n}: faces {nf}, lambda {lam}, OPT {opt}, greedy {gr}, light theta T* {T}, OPT==min: {min(gr,T)==opt}, edges per strand <= {int(np.ceil(lam/min(w.values())))-1}")
