"""Test candidate families of parts on the hard-instance bank.

For a family X of vertex sets, val(X) = min over X in X of d(X) + lambda(G[V - X]);
the family 'hits' an instance if val = OPT (some optimum has a part in the family).
"""
import itertools, json, sys
import numpy as np
from cutlib import (cut_table, tolerance, optimum, labelings, gomory_hu_tree, tree_sides,
                    induced_lambda, popcount)


class Inst:
    def __init__(self, n, E):
        self.n, self.E = n, E
        self.d = cut_table(n, E)
        self.tol = tolerance(E)
        self.full = (1 << n) - 1
        self.opt, idx, _ = optimum(n, E, self.tol)
        _, M = labelings(n)
        self.optima = [tuple(int(x) for x in M[i]) for i in idx]
        self.optparts = {p for P in self.optima for p in P}
        self.masks = np.arange(1 << n, dtype=np.int64)
        self.size = np.array([popcount(S) for S in range(1 << n)])
        self._tree = None

    @property
    def tree(self):
        if self._tree is None:
            self._tree = gomory_hu_tree(self.n, self.d, self.tol)
        return self._tree

    def val(self, fam):
        best = np.inf
        for X in fam:
            R = self.full ^ X
            if X == 0 or popcount(R) < 2:
                continue
            best = min(best, float(self.d[X]) + induced_lambda(self.d, R))
        return best

    def hits(self, fam):
        return self.val(fam) <= self.opt + self.tol

    def extreme_minimizers(self, ok):
        """Minimal and maximal sets among the minimum-weight sets with ok[S] true."""
        idx = np.flatnonzero(ok)
        if len(idx) == 0:
            return []
        v = self.d[idx]
        mins = idx[v <= v.min() + self.tol]
        return [int(np.bitwise_and.reduce(mins)), int(np.bitwise_or.reduce(mins))]

    def contains(self, X):
        return (self.masks & X) == X

    def avoids(self, X):
        return (self.masks & X) == 0


# ------------------------------------------------------------------ families
def fam_sides(I):
    return set(tree_sides(I.n, I.tree))


def fam_singletons(I):
    return {1 << v for v in range(I.n)}


def fam_pair_root(I, r):
    out = set()
    for x, y in itertools.combinations([v for v in range(I.n) if v != r], 2):
        ok = I.contains((1 << x) | (1 << y)) & I.avoids(1 << r)
        out.update(I.extreme_minimizers(ok))
    return out


def fam_one_root(I, r):
    """For each x != r: lightest sets containing x, avoiding r, with >= 2 vertices."""
    out = set()
    for x in range(I.n):
        if x == r:
            continue
        ok = I.contains(1 << x) & I.avoids(1 << r) & (I.size >= 2)
        out.update(I.extreme_minimizers(ok))
    return out


def fam_isolating(I):
    out = set()
    for a in range(I.n):
        for b, c in itertools.combinations([v for v in range(I.n) if v != a], 2):
            ok = I.contains(1 << a) & I.avoids((1 << b) | (1 << c))
            out.update(I.extreme_minimizers(ok))
    return out


def fam_nontriv_vertex(I):
    """For each x: lightest sets containing x with at least two vertices on each side."""
    out = set()
    nt = (I.size >= 2) & (I.size <= I.n - 2)
    for x in range(I.n):
        out.update(I.extreme_minimizers(I.contains(1 << x) & nt))
    return out


def fam_nontriv_pair_sep(I):
    """For each pair x, y: lightest nontrivial sets containing x but not y."""
    out = set()
    nt = (I.size >= 2) & (I.size <= I.n - 2)
    for x in range(I.n):
        for y in range(I.n):
            if x != y:
                out.update(I.extreme_minimizers(I.contains(1 << x) & I.avoids(1 << y) & nt))
    return out


def fam_nontriv_pair_in(I):
    """For each pair x, y: lightest nontrivial sets containing both."""
    out = set()
    nt = (I.size >= 2) & (I.size <= I.n - 2)
    for x, y in itertools.combinations(range(I.n), 2):
        out.update(I.extreme_minimizers(I.contains((1 << x) | (1 << y)) & nt))
    return out


def fam_NI(I):
    """Cuts in nondecreasing order of weight up to and including the first one that crosses
    an earlier (lighter or equal) cut; each cut represented by both sides."""
    n, full = I.n, I.full
    S = np.arange(1, 1 << (n - 1), dtype=np.int64)          # sides not containing vertex n-1
    order = S[np.argsort(I.d[S], kind="stable")]
    fam, seen = set(), []
    for X in order:
        X = int(X)
        crosses = any((X & Y) and (X & ~Y & full) and (Y & ~X & full) and (full & ~(X | Y))
                      for Y in seen)
        fam |= {X, full ^ X}
        seen.append(X)
        if crosses:
            break
    return fam


def main(path="bank.json"):
    bank = json.load(open(path))
    names = ["sides", "sides+singletons", "NI prefix", "isolating (a vs b,c)",
             "pair-vs-root, every root", "pair-vs-root+singletons, every root",
             "pair-vs-root+singletons+sides, every root",
             "one-root+singletons, every root", "one-root+singletons+sides, every root",
             "nontriv-vertex+singletons+sides", "nontriv-pair-sep+singletons+sides",
             "nontriv-pair-in+singletons+sides"]
    stats = {k: {} for k in names}
    sizes = {k: [] for k in names}
    for b in bank:
        I = Inst(b["n"], [tuple(e) for e in b["E"]])
        sd, sg = fam_sides(I), fam_singletons(I)
        res = {"sides": I.hits(sd), "sides+singletons": I.hits(sd | sg)}
        ni = fam_NI(I); res["NI prefix"] = I.hits(ni); sizes["NI prefix"].append(len(ni))
        iso = fam_isolating(I); res["isolating (a vs b,c)"] = I.hits(iso)
        sizes["isolating (a vs b,c)"].append(len(iso))
        for key, fam in (("nontriv-vertex", fam_nontriv_vertex), ("nontriv-pair-sep", fam_nontriv_pair_sep),
                         ("nontriv-pair-in", fam_nontriv_pair_in)):
            f = fam(I); res[key + "+singletons+sides"] = I.hits(f | sg | sd)
            sizes.setdefault(key, []).append(len(f))
        for key, fam in (("pair-vs-root", fam_pair_root), ("one-root", fam_one_root)):
            allr = {"": True, "+singletons": True, "+singletons+sides": True}
            for r in range(I.n):
                f = fam(I, r)
                if key == "pair-vs-root":
                    allr[""] &= I.hits(f)
                allr["+singletons"] &= I.hits(f | sg)
                allr["+singletons+sides"] &= I.hits(f | sg | sd)
                sizes.setdefault(f"{key} size", []).append(len(f))
            for suf, v in allr.items():
                k = f"{key}{suf}, every root"
                if k in stats:
                    res[k] = v
        for k, v in res.items():
            s = stats[k].setdefault(b["kind"], [0, 0])
            s[0] += v; s[1] += 1
    kinds = sorted({b["kind"] for b in bank})
    print("family".ljust(46) + "".join(k.rjust(14) for k in kinds))
    for k in names:
        print(k.ljust(46) + "".join((f"{stats[k].get(kd, [0, 0])[0]}/{stats[k].get(kd, [0, 0])[1]}").rjust(14)
                                    for kd in kinds))
    for k, v in sizes.items():
        if v:
            print(f"mean size {k}: {np.mean(v):.1f} (max {max(v)})")


if __name__ == "__main__":
    main(*sys.argv[1:])
