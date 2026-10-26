"""Independent exhaustive verification of Theorem 9 (exact integer arithmetic).

Reads the instance from ../lean/theorem9_instance.json (the same file used by the Lean
generator), scales the weights to integers, and checks every claim of Theorem 9:
  * the weighted edge connectivity lambda;
  * the unique minimum-weight 3-partition, its value OPT, and its hardness;
  * the Gomory-Hu cut tree T is unique among all n^(n-2) labelled spanning trees
    (enumerated by Pruefer codes), and each tree edge has a unique minimum-weight cut;
  * F(T) > OPT, and no part of the optimum is a side of T.
Usage: python3 verify_theorem9.py [instance.json]. Runtime: a few seconds.
"""
import itertools, json, sys
from decimal import Decimal
from pathlib import Path
import numpy as np
from cutlib import (cut_table, edge_connectivity, optimum, labelings, pair_weight,
                    fundamental_side, kapoor_F, tree_sides, min_cut_between)


def pruefer_trees(n):
    for seq in itertools.product(range(n), repeat=n - 2):
        deg = [1] * n
        for x in seq:
            deg[x] += 1
        edges = []
        for x in seq:
            leaf = min(i for i in range(n) if deg[i] == 1)
            edges.append((leaf, x)); deg[leaf] -= 1; deg[x] -= 1
        u, v = [i for i in range(n) if deg[i] == 1]
        edges.append((u, v))
        yield edges


def main(path):
    inst = json.loads(Path(path).read_text(encoding="utf-8"))
    V = inst["vertices"]; n = len(V); ix = {v: i for i, v in enumerate(V)}
    scale = int(inst.get("scale", 1))
    E = [(ix[a], ix[b], int(Decimal(str(w)) * scale)) for a, b, w in inst["edges"]]
    txt = lambda x: f"{Decimal(int(x)) / scale}"
    name = lambda S: "{" + ",".join(V[i] for i in range(n) if (S >> i) & 1) + "}"
    d = cut_table(n, E)                      # integer-valued floats: exact
    full = (1 << n) - 1
    ok = True

    def check(cond, msg):
        nonlocal ok
        print(("  ok    " if cond else "  FAIL  ") + msg)
        ok &= bool(cond)

    lam = edge_connectivity(n, d)
    print(f"lambda = {txt(lam)}")
    opt, idx, _ = optimum(n, E, 0)
    _, M = labelings(n)
    check(len(idx) == 1, f"unique minimum-weight 3-partition, OPT = {txt(opt)}")
    A, B, C = (int(x) for x in M[idx[0]])
    pws = [pair_weight(d, A, B), pair_weight(d, A, C), pair_weight(d, B, C)]
    print(f"optimum {name(A)}, {name(B)}, {name(C)}; pair weights " + ", ".join(txt(p) for p in pws))
    check(max(pws) < lam, "optimum is hard (all pair weights below lambda)")
    lxy = {(x, y): min_cut_between(n, d, x, y) for x in range(n) for y in range(n) if x != y}
    trees = [t for t in pruefer_trees(n)
             if all(d[fundamental_side(n, [(a, b, 0) for a, b in t], a, b)] == lxy[(a, b)] for a, b in t)]
    check(len(trees) == 1, f"exactly one Gomory-Hu cut tree among {n ** (n - 2)} labelled spanning trees")
    tree = [(a, b, lxy[(a, b)]) for a, b in trees[0]]
    print("tree T: " + ", ".join(f"{V[a]}-{V[b]} ({txt(w)})" for a, b, w in tree))
    uniq = True
    for a, b, w in tree:
        cnt = sum(1 for S in range(1 << n) if (S >> a) & 1 and not (S >> b) & 1 and d[S] == w)
        uniq &= cnt == 1
    check(uniq, "each tree edge has a unique minimum-weight cut")
    F = kapoor_F(n, d, tree)
    sides = tree_sides(n, tree)
    check(F > opt, f"F(T) = {txt(F)} > OPT = {txt(opt)} (gap {txt(F - opt)})")
    check(not any(X in sides for X in (A, B, C)), "no part of the optimum is a side of T")
    print("RESULT:", "all claims of Theorem 9 verified" if ok else "SOME CLAIMS FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    default = Path(__file__).resolve().parent.parent / "lean" / "theorem9_instance.json"
    sys.exit(main(sys.argv[1] if len(sys.argv) > 1 else default))
