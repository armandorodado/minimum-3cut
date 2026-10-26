"""Exact small-graph routines shared by the verification scripts.

All quantities are computed by exhaustive enumeration over vertex subsets, so the
scripts are meant for graphs with at most about 13 vertices. A graph is given as
(n, edges) with vertices 0..n-1 and edges a list of (u, v, w), w > 0.
A vertex set is an integer bitmask: vertex i belongs to S iff bit i of S is set.

Gomory-Hu (cut) trees are built by the classical contraction method of Gomory and
Hu (1961), with every minimum cut found by exhaustive search over vertex sets (no
max-flow code, hence no floating-point residual issues). Every tree returned is
re-verified: each tree edge's fundamental side must be a minimum-weight cut between
the edge's endpoints.
"""
from functools import lru_cache
import itertools
import numpy as np
import networkx as nx
from scipy.spatial import Delaunay

INF = float("inf")


def tolerance(edges):
    """Absolute tolerance for comparing sums of the edge weights."""
    total = sum(w for _, _, w in edges)
    return 1e-9 * max(1.0, total)


def popcount(m):
    return bin(m).count("1")


# ----------------------------------------------------------------------------- cuts
def cut_table(n, edges):
    """d(S) for every vertex set S, as an array indexed by bitmask."""
    masks = np.arange(1 << n, dtype=np.int64)
    d = np.zeros(1 << n)
    for u, v, w in edges:
        d += w * (((masks >> u) ^ (masks >> v)) & 1)
    return d


def edge_connectivity(n, d):
    """Weighted edge connectivity lambda = least total weight of a cut."""
    return float(d[1:(1 << n) - 1].min())


def global_min_cuts(n, d, tol):
    """All global minimum-weight cuts, each bipartition once (the side containing vertex 0)."""
    lam = edge_connectivity(n, d)
    full = (1 << n) - 1
    return lam, [S for S in range(1, full) if S & 1 and d[S] <= lam + tol]


def induced_lambda(d, U):
    """Least weight of a bipartition of G[U] into two nonempty sets; inf if |U| = 1.

    The weight of the edges of G[U] between X and U minus X is (d(X) + d(U-X) - d(U)) / 2.
    """
    if popcount(U) < 2:
        return INF
    low = U & -U  # fix the lowest vertex of U on the X side: each bipartition once
    best = INF
    rest = U ^ low
    sub = rest
    while True:
        X = sub | low
        if X != U:
            best = min(best, (d[X] + d[U ^ X] - d[U]) / 2.0)
        if sub == 0:
            break
        sub = (sub - 1) & rest
    return max(best, 0.0)


def greedy_value(n, d, S):
    """greedy(S) = lambda + min(lambda(G[S]), lambda(G[V-S])) for a global minimum-weight cut S."""
    full = (1 << n) - 1
    return float(d[S]) + min(induced_lambda(d, S), induced_lambda(d, full ^ S))


def pair_weight(d, X, Y):
    """Weight of the edges joining disjoint vertex sets X and Y."""
    return (d[X] + d[Y] - d[X | Y]) / 2.0


# ----------------------------------------------------------------------------- 3-partitions
@lru_cache(maxsize=None)
def labelings(n):
    """All 3-partitions of {0..n-1}, each once: label array (rows) and the three part masks.

    Canonical form: vertex 0 has label 0, and label 1 occurs before label 2.
    """
    L = np.array(list(itertools.product(range(3), repeat=n - 1)), dtype=np.int8)
    L = np.hstack([np.zeros((len(L), 1), np.int8), L])
    ok = (L == 1).any(1) & (L == 2).any(1)
    ok &= np.argmax(L == 1, 1) < np.argmax(L == 2, 1)
    L = L[ok]
    pw = (1 << np.arange(n)).astype(np.int64)
    M = np.stack([((L == k) * pw).sum(1) for k in range(3)], axis=1)
    return L, M


def partition_weights(n, edges):
    """W(A,B,C) for every canonical 3-partition, aligned with labelings(n)."""
    L, _ = labelings(n)
    W = np.zeros(len(L))
    for u, v, w in edges:
        W += w * (L[:, u] != L[:, v])
    return W


def optimum(n, edges, tol):
    """OPT and the indices (into labelings(n)) of all minimum-weight 3-partitions."""
    W = partition_weights(n, edges)
    opt = float(W.min())
    return opt, np.flatnonzero(W <= opt + tol), W


def is_hard(d, parts, lam, tol):
    """All three pair weights of the 3-partition (A, B, C) are below lambda."""
    A, B, C = (int(x) for x in parts)
    return max(pair_weight(d, A, B), pair_weight(d, A, C), pair_weight(d, B, C)) < lam - tol


# ----------------------------------------------------------------------------- Gomory-Hu trees
def min_cut_between(n, d, x, y):
    """lambda(x, y): least weight of a cut separating x from y."""
    masks = np.arange(1 << n, dtype=np.int64)
    sep = ((masks >> x) & 1) != ((masks >> y) & 1)
    return float(d[sep].min())


def gomory_hu_tree(n, d, tol):
    """A Gomory-Hu cut tree, as a list of edges (x, y, w) between vertices.

    Classical contraction construction; minimum cuts in the contracted graphs are found
    exhaustively as the lightest vertex sets that keep each contracted group on one side.
    The result is verified before it is returned.
    """
    masks = np.arange(1 << n, dtype=np.int64)
    sup = {0: frozenset(range(n))}        # supernode id -> vertex set
    adj = {0: {}}                          # supernode id -> {neighbour id: weight}
    nxt = 1
    while True:
        S = next((k for k, vs in sorted(sup.items()) if len(vs) >= 2), None)
        if S is None:
            break
        s, t = sorted(sup[S])[:2]
        # vertex groups: one per component of the tree with S removed
        groups = []
        for nb in adj[S]:
            seen, stack = {nb}, [nb]
            while stack:
                a = stack.pop()
                for b in adj[a]:
                    if b != S and b not in seen:
                        seen.add(b)
                        stack.append(b)
            groups.append((nb, sum(1 << v for k in seen for v in sup[k])))
        ok = (((masks >> s) & 1) == 1) & (((masks >> t) & 1) == 0)
        for _, g in groups:
            inter = masks & g
            ok &= (inter == 0) | (inter == g)
        cand = np.flatnonzero(ok)
        best = cand[np.argmin(d[cand])]
        val = float(d[best])
        S1 = frozenset(v for v in sup[S] if (best >> v) & 1)
        S2 = sup[S] - S1
        a, b = nxt, nxt + 1
        nxt += 2
        sup[a], sup[b] = S1, S2
        adj[a], adj[b] = {b: val}, {a: val}
        for nb, g in groups:
            w = adj[S][nb]
            side = a if (best & g) == g else b
            del adj[nb][S]
            adj[nb][side] = w
            adj[side][nb] = w
        del sup[S], adj[S]
    vert = {k: next(iter(vs)) for k, vs in sup.items()}
    tree = sorted({(min(vert[a], vert[b]), max(vert[a], vert[b]), w)
                   for a in adj for b, w in adj[a].items()})
    verify_cut_tree(n, d, tree, tol)
    return tree


def fundamental_side(n, tree, x, y):
    """Vertex set of the component of tree minus edge {x, y} that contains x."""
    nbr = {v: [] for v in range(n)}
    for a, b, _ in tree:
        if {a, b} != {x, y}:
            nbr[a].append(b)
            nbr[b].append(a)
    seen, stack = {x}, [x]
    while stack:
        a = stack.pop()
        for b in nbr[a]:
            if b not in seen:
                seen.add(b)
                stack.append(b)
    return sum(1 << v for v in seen)


def verify_cut_tree(n, d, tree, tol):
    """Raise unless tree is a spanning tree whose edges are minimum-weight cuts."""
    T = nx.Graph()
    T.add_nodes_from(range(n))
    T.add_edges_from((a, b) for a, b, _ in tree)
    if T.number_of_edges() != n - 1 or not nx.is_connected(T):
        raise AssertionError("not a spanning tree")
    for x, y, w in tree:
        F = fundamental_side(n, tree, x, y)
        if abs(d[F] - w) > tol or abs(min_cut_between(n, d, x, y) - w) > tol:
            raise AssertionError(f"tree edge {x}-{y} is not a minimum-weight cut")


def tree_sides(n, tree):
    """All Gomory-Hu sides: fundamental sides of the tree edges and their complements."""
    full = (1 << n) - 1
    out = set()
    for x, y, _ in tree:
        F = fundamental_side(n, tree, x, y)
        out |= {F, full ^ F}
    return out


def kapoor_F(n, d, tree):
    """F(T): least weight of a 3-partition one of whose parts is a side of T."""
    full = (1 << n) - 1
    best = INF
    for X in tree_sides(n, tree):
        if popcount(full ^ X) >= 2:
            best = min(best, float(d[X]) + induced_lambda(d, full ^ X))
    return best


# ----------------------------------------------------------------------------- k-partitions
@lru_cache(maxsize=None)
def k_partitions(n, k):
    """All partitions of {0..n-1} into exactly k blocks, as label rows (restricted growth strings)."""
    out = []

    def rec(i, lab, m):
        if i == n:
            if m == k:
                out.append(lab.copy())
            return
        if m + (n - i) < k:
            return
        for c in range(min(m + 1, k)):
            lab.append(c)
            rec(i + 1, lab, max(m, c + 1))
            lab.pop()

    rec(0, [], 0)
    return np.array(out, dtype=np.int8)


def k_partition_weights(n, k, edges):
    L = k_partitions(n, k)
    W = np.zeros(len(L))
    for u, v, w in edges:
        W += w * (L[:, u] != L[:, v])
    return L, W


def compatible(L, S, n):
    """Rows of L whose every block lies inside S or inside its complement."""
    s = np.array([(S >> i) & 1 for i in range(n)], dtype=np.int8)
    ok = np.ones(len(L), bool)
    for b in range(int(L.max()) + 1):
        inb = L == b
        ok &= ~((inb & (s == 0)).any(1) & (inb & (s == 1)).any(1))
    return ok


# ----------------------------------------------------------------------------- generators
def to_instance(G):
    """(n, edges) from a networkx graph, relabelled 0..n-1."""
    nodes = sorted(G.nodes())
    ix = {v: i for i, v in enumerate(nodes)}
    return len(nodes), [(ix[u], ix[v], float(d["weight"])) for u, v, d in G.edges(data=True)]


def random_planar(n, keep, rng, integer=False):
    """Delaunay triangulation of n random points, each edge kept with probability keep."""
    while True:
        pts = rng.random((n, 2))
        tri = Delaunay(pts)
        E = set()
        for s in tri.simplices:
            for a, b in ((s[0], s[1]), (s[1], s[2]), (s[0], s[2])):
                E.add((min(a, b), max(a, b)))
        G = nx.Graph()
        G.add_nodes_from(range(n))
        for (a, b) in sorted(E):
            if rng.random() < keep:
                G.add_edge(int(a), int(b))
        if nx.is_connected(G) and G.number_of_edges() >= n:
            break
    for u, v in G.edges():
        G[u][v]["weight"] = float(rng.integers(1, 6)) if integer else float(rng.uniform(1, 10))
    return G


def random_general(n, p, rng, integer=False):
    """Connected G(n, p) with weights uniform in [1, 10] (or integers 1..5)."""
    while True:
        G = nx.gnp_random_graph(n, p, seed=int(rng.integers(1 << 30)))
        if nx.is_connected(G):
            break
    for u, v in G.edges():
        G[u][v]["weight"] = float(rng.integers(1, 6)) if integer else float(rng.uniform(1, 10))
    return G


def structured(kind, n, rng):
    """Near-complete, circulant, three-cluster and wheel graphs (mostly star-shaped Gomory-Hu trees)."""
    G = nx.Graph()
    if kind == "near-complete":
        for u, v in itertools.combinations(range(n), 2):
            G.add_edge(u, v, weight=float(rng.uniform(1, 1.5)))
    elif kind == "circulant":
        ks = rng.choice(range(1, n // 2 + 1), size=2, replace=False)
        for u in range(n):
            for k in ks:
                G.add_edge(u, (u + int(k)) % n, weight=float(rng.uniform(1, 2)))
    elif kind == "clusters":
        parts = np.array_split(rng.permutation(n), 3)
        for P in parts:
            for u, v in itertools.combinations(P, 2):
                G.add_edge(int(u), int(v), weight=float(rng.uniform(0.5, 3)))
        for u, v in itertools.combinations(range(n), 2):
            if not G.has_edge(u, v) and rng.random() < 0.35:
                G.add_edge(u, v, weight=float(rng.uniform(0.5, 3)))
    elif kind == "wheel":
        G = nx.wheel_graph(n)
        for u, v in G.edges():
            G[u][v]["weight"] = float(rng.uniform(1, 3))
    else:
        raise ValueError(kind)
    return G if nx.is_connected(G) else None


def random_instance(t, rng, n_lo=6, n_hi=10):
    """The mixed random family used throughout: planar/general x real/integer weights."""
    planar, integer = t % 2 == 0, (t // 2) % 2 == 0
    n = int(rng.integers(n_lo, n_hi + 1))
    G = random_planar(n, 0.8, rng, integer) if planar else random_general(n, 0.45, rng, integer)
    return to_instance(G)
