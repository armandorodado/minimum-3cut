"""How well can a candidate part other than a cluster (or its complement) do in G_pi?

For the cluster graphs of lowerbound.py (inner weight ALPHA, inter-cluster BETA, plus the
fixed perturbation H), compute for every vertex set X
    f(X) = least weight of a 3-partition having X as a part,
and report rho = min{ f(X) : X not a cluster or the complement of one } / OPT.
Any family that contains no cluster and no complement of a cluster therefore gives at best
a rho-approximation. Exact integer arithmetic.
Usage: python3 ratio.py m beta_scaled  (weights: ALPHA = 100000, BETA = beta_scaled)
"""
import itertools, sys
import numpy as np
from cutlib import labelings, partition_weights, cut_table, edge_connectivity


def main(m, beta):
    n = 3 * m
    pi = np.repeat(np.arange(3), m)
    E = []
    for u, v in itertools.combinations(range(n), 2):
        E.append((u, v, (100000 if pi[u] == pi[v] else beta) + u + v))
    L, M = labelings(n)
    W = partition_weights(n, E)
    f = np.full(1 << n, np.inf)
    for k in range(3):
        np.minimum.at(f, M[:, k], W)
    opt = W.min()
    clusters = [sum(1 << v for v in range(n) if pi[v] == k) for k in range(3)]
    full = (1 << n) - 1
    special = set(clusters) | {full ^ c for c in clusters}
    g = f.copy()
    for s in special:
        g[s] = np.inf
    X = int(np.argmin(g))
    d = cut_table(n, E)
    lam = edge_connectivity(n, d)
    print(f"m={m} beta={beta/100000:.4f}: OPT={opt:.0f} (clusters: {sorted(int(x) for x in M[np.argmin(W)]) == sorted(clusters)}), "
          f"unique={int((W == opt).sum()) == 1}, lambda={lam:.0f}, "
          f"best non-cluster part {bin(X).count('1')} vertices, rho={g[X]/opt:.4f}, "
          f"min-cut ok={d[[S for S in range(1, full) if 2 <= bin(S).count('1') <= n - 2]].min() > max(d[1 << v] for v in range(n))}")


if __name__ == "__main__":
    main(int(sys.argv[1]), int(sys.argv[2]))
