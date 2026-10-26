import json, sys, itertools, numpy as np
sys.path.insert(0,'.')
from families import Inst, fam_sides, fam_singletons, fam_NI
from cutlib import edge_connectivity, is_hard

def sw_family(I, starts_rng=None):
    W = np.zeros((I.n, I.n))
    for u, v, w in I.E: W[u, v] += w; W[v, u] += w
    groups = {v: 1 << v for v in range(I.n)}; out = set(groups.values()); active = list(range(I.n))
    while len(active) > 1:
        st = active[0] if starts_rng is None else active[int(starts_rng.integers(len(active)))]
        a = [st]; rest = set(active) - {st}; conn = {v: W[st, v] for v in rest}
        while rest:
            z = max(rest, key=lambda v: (conn[v], -v)); a.append(z); rest.remove(z)
            for v in rest: conn[v] += W[z, v]
        s, t = a[-2], a[-1]
        out.add(groups[t]); groups[s] |= groups[t]; out.add(groups[s])
        W[s, :] += W[t, :]; W[:, s] += W[:, t]; W[s, s] = 0; active.remove(t)
    return out | {I.full ^ X for X in out if X != I.full}

for f in sys.argv[1:]:
    for inst in json.load(open(f)):
        if inst['sw_hits']: continue
        I = Inst(inst['n'], [tuple(e) for e in inst['E']])
        lam = edge_connectivity(I.n, I.d)
        hard = all(is_hard(I.d, P, lam, I.tol) for P in I.optima)
        sd, sg = fam_sides(I), fam_singletons(I)
        base = sw_family(I)
        rng = np.random.default_rng(0)
        miss_starts = sum(not I.hits(sw_family(I, rng)) for _ in range(200))
        print(f, 'n', I.n, 'optimum parts', [bin(p).count('1') for p in I.optima[0]], 'hard', hard,
              '| SW alone hits', I.hits(base), '| SW+sides+singletons hits', I.hits(base|sd|sg),
              '| random start vertices: SW misses in', miss_starts, 'of 200 runs',
              '| sides alone hit', I.hits(sd))
