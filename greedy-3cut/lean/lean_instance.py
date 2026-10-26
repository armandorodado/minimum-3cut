#!/usr/bin/env python3
"""Check a 7-vertex instance for the Theorem 9 properties and generate its Lean proof.

Usage:
    python3 lean_instance.py INSTANCE.json                  # report only
    python3 lean_instance.py INSTANCE.json -o Out.lean      # report, then write the Lean file

INSTANCE.json:
    {
      "name": "MyInstance",            # Lean namespace (letters, digits, _)
      "scale": 1000000,                # weights are multiplied by this to get integers
      "vertices": ["s", "u0", ...],    # exactly 7 names; the first is the root of T
      "edges": [["s", "u0", "0.364863"], ...]   # weights as decimal strings or numbers
    }
Optional keys: "title_suffix", "weight_note".

The Lean file is written only if every claim of Theorem 9 holds, because otherwise
some of its theorems would be false and Lean would (correctly) reject them:
  - the minimum-weight 3-partition is unique and hard (all pair weights < lambda);
  - the Gomory-Hu (cut) tree T is unique, and each of its edges has a unique
    minimum-weight cut;
  - F(T), the least weight of a 3-partition having a side of T as a part, exceeds OPT.
The generated file is then checked with `lean Out.lean` (about 13 minutes).
"""
import argparse, itertools, json, re, sys
from decimal import Decimal
from pathlib import Path

N = 7
FULL = (1 << N) - 1
TEMPLATE = Path(__file__).with_name("Theorem9.template.lean")


def load(path):
    inst = json.loads(Path(path).read_text(encoding="utf-8"))
    V = inst["vertices"]
    if len(V) != N or len(set(V)) != N:
        sys.exit("error: exactly 7 distinct vertex names are required")
    ix = {v: i for i, v in enumerate(V)}
    scale = int(inst.get("scale", 1))
    E = {}
    for u, v, w in inst["edges"]:
        if u not in ix or v not in ix or u == v:
            sys.exit(f"error: bad edge {u}-{v}")
        wi = Decimal(str(w)) * scale
        if wi != wi.to_integral_value() or wi <= 0:
            sys.exit(f"error: weight {w} of {u}-{v} is not a positive multiple of 1/{scale}")
        key = (ix[u], ix[v])
        if key in E or key[::-1] in E:
            sys.exit(f"error: duplicate edge {u}-{v}")
        E[key] = int(wi)
    return inst, V, scale, E


def analyse(V, E):
    cut = [0] * (1 << N)
    for S in range(1 << N):
        cut[S] = sum(w for (a, b), w in E.items() if ((S >> a) & 1) != ((S >> b) & 1))
    lam = min(cut[S] for S in range(1, FULL))
    lamset = min(S for S in range(1, FULL) if cut[S] == lam)
    lxy = [[0 if x == y else min(cut[S] for S in range(1 << N) if ((S >> x) & 1) != ((S >> y) & 1))
            for y in range(N)] for x in range(N)]

    def lab(c, i): return c // 3 ** i % 3
    def W(c): return sum(w for (a, b), w in E.items() if lab(c, a) != lab(c, b))
    def blocks(c): return [sum(1 << i for i in range(N) if lab(c, i) == k) for k in range(3)]
    parts = [c for c in range(3 ** N) if len({lab(c, i) for i in range(N)}) == 3]
    opt = min(W(c) for c in parts)
    optp = {frozenset(blocks(c)) for c in parts if W(c) == opt}

    # all cut trees, as parent lists rooted at vertex 0
    def subtree(P, i):
        out = 0
        for j in range(N):
            k = j
            for _ in range(N):
                if k == i: out |= 1 << j; break
                if k == 0: break
                k = P[k]
        return out
    def is_tree(P):
        for j in range(1, N):
            k, steps = j, 0
            while k != 0 and steps < 6: k, steps = P[k], steps + 1
            if k != 0: return False
        return True
    trees = []
    for ps in itertools.product(range(N), repeat=N - 1):
        P = (0,) + ps
        if is_tree(P) and all(cut[subtree(P, i)] == lxy[i][P[i]] for i in range(1, N)):
            trees.append(P)
    return dict(cut=cut, lam=lam, lamset=lamset, lxy=lxy, lab=lab, W=W, blocks=blocks,
                parts=parts, opt=opt, optp=optp, trees=trees, subtree=subtree)


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("instance")
    ap.add_argument("-o", "--out", help="write the Lean proof to this file")
    args = ap.parse_args()
    inst, V, scale, E = load(args.instance)
    A = analyse(V, E)
    cut, lam, opt, lab, W, blocks = A["cut"], A["lam"], A["opt"], A["lab"], A["W"], A["blocks"]
    digits = len(str(scale)) - 1 if scale > 1 else 0
    txt = lambda x: f"{Decimal(x) / scale:.{digits}f}"
    name = lambda S: "{" + ",".join(V[i] for i in range(N) if (S >> i) & 1) + "}"
    ok = True
    def check(cond, msg):
        nonlocal ok
        print(("  ok    " if cond else "  FAIL  ") + msg)
        ok &= bool(cond)

    print(f"Instance '{inst.get('name', 'Theorem9')}': {len(E)} edges, total weight {txt(sum(E.values()))}")
    print(f"  lambda = {txt(lam)}, attained by {name(A['lamset'])}")
    check(all(cut[S] > 0 for S in range(1, FULL)), "graph is connected")
    check(len(A["optp"]) == 1, f"minimum-weight 3-partition is unique (OPT = {txt(opt)}; {len(A['optp'])} optimum/optima)")
    copt = next(c for c in A["parts"] if W(c) == opt)
    # canonical labelling: vertex 0 gets label 0, then labels in order of first appearance
    order = []
    for i in range(N):
        if lab(copt, i) not in order: order.append(lab(copt, i))
    relabel = {old: new for new, old in enumerate(order)}
    copt = sum(relabel[lab(copt, i)] * 3 ** i for i in range(N))
    MA, MB, MC = blocks(copt)
    pw = lambda X, Y: sum(w for (a, b), w in E.items()
                          if ((X >> a) & 1 and (Y >> b) & 1) or ((Y >> a) & 1 and (X >> b) & 1))
    WAB, WAC, WBC = pw(MA, MB), pw(MA, MC), pw(MB, MC)
    print(f"  optimum: {name(MA)}, {name(MB)}, {name(MC)}; pair weights {txt(WAB)}, {txt(WAC)}, {txt(WBC)}")
    check(max(WAB, WAC, WBC) < lam, "optimum is hard (every pair weight < lambda)")
    check(len(A["trees"]) == 1, f"Gomory-Hu cut tree is unique ({len(A['trees'])} found)")
    if not A["trees"]:
        sys.exit("no cut tree found (should be impossible)")
    PT = A["trees"][0]
    subs = [A["subtree"](PT, i) for i in range(1, N)]
    print("  tree T: " + ", ".join(f"{V[i]}–{V[PT[i]]} ({txt(cut[subs[i-1]])})" for i in range(1, N)))
    uniq = all(sum(1 for S in range(1 << N) if (S >> i) & 1 and not (S >> PT[i]) & 1
                   and cut[S] == cut[subs[i - 1]]) == 1 for i in range(1, N))
    check(uniq, "each tree edge has a unique minimum-weight cut")
    sides = set(subs) | {FULL ^ S for S in subs}
    with_side = [c for c in A["parts"] if any(B in sides for B in blocks(c))]
    FT = min(W(c) for c in with_side)
    wit = min(c for c in with_side if W(c) == FT)
    check(FT > opt, f"F(T) = {txt(FT)} exceeds OPT = {txt(opt)} (gap {txt(FT - opt)})")
    if not ok:
        print("\nNot every claim of Theorem 9 holds for this instance; no Lean file written.")
        sys.exit(1)
    print("All claims hold.")
    if not args.out:
        return

    ns = inst.get("name", "Theorem9")
    if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", ns):
        sys.exit("error: 'name' must be a valid Lean identifier")
    items = [f"({a},{b},{w})" for (a, b), w in E.items()]
    edge_lines = ["  [" + ", ".join(items[:5])] + ["   " + ", ".join(items[k:k + 5]) for k in range(5, len(items), 5)]
    edges_txt = (",\n".join(edge_lines)) + "]"
    rows = [", ".join(str(A["lxy"][x][y]) for y in range(N)) for x in range(N)]
    lamtab = "  [" + ",\n   ".join(rows) + "]"
    pnames = ["a", "b", "p₃", "p₄", "p₅", "p₆"]
    fills = {
        "NS": ns,
        "TITLE_SUFFIX": inst.get("title_suffix", f" (instance `{ns}`)"),
        "WEIGHT_NOTE": inst.get("weight_note",
            f"Weights are the instance's weights multiplied by `{scale}`,\nso all arithmetic is on natural numbers."),
        "LEGEND": ", ".join(f"{i} = {v}" for i, v in enumerate(V)),
        "NEDGES": str(len(E)),
        "UNIT_NOTE": f", weights in units of `10^-{digits}`" if digits else "",
        "EDGES": edges_txt,
        "LAM": str(lam), "LAM_TXT": txt(lam),
        "LAMSET": str(A["lamset"]), "LAMSET_DESC": name(A["lamset"]),
        "OPT_DESC": f"({name(MA)}, {name(MB)}, {name(MC)})",
        "OPT_LABELS": ",".join(str(lab(copt, i)) for i in range(N)),
        "COPT": str(copt), "OPT": str(opt), "OPT_TXT": txt(opt),
        "PARTS_DESC": f"`{name(MA)} = {MA}`, `{name(MB)} = {MB}`, `{name(MC)} = {MC}`",
        "MA": str(MA), "MB": str(MB), "MC": str(MC),
        "WAB": str(WAB), "WAC": str(WAC), "WBC": str(WBC),
        "LAMTAB": lamtab, "BIG": str(sum(E.values()) + 1),
        "TREE_DESC": ", ".join(f"{V[PT[i]]}–{V[i]}" for i in range(1, N)),
        "PT": "[" + ", ".join(map(str, PT)) + "]",
        "SIDES_DESC": ", ".join(name(S) for S in subs),
        "SIDES": "(" + ", ".join(map(str, subs)) + ")",
        "DSIDES": "(" + ", ".join(f"d {S}" for S in subs) + ")",
        "SIDEW": "(" + ", ".join(str(cut[S]) for S in subs) + ")",
        "PTBEQ": " && ".join(f"Nat.beq {p} {PT[i + 1]}" for i, p in enumerate(pnames)),
        "FT": str(FT), "FT_TXT": txt(FT),
        "WIT": str(wit),
        "WIT_DESC": "(" + ", ".join(name(B) for B in blocks(wit)) + ")",
        "WIT_LABELS": ",".join(str(lab(wit, i)) for i in range(N)),
    }
    out = TEMPLATE.read_text(encoding="utf-8")
    for k, v in fills.items():
        out = out.replace("{{" + k + "}}", v)
    left = re.findall(r"\{\{[A-Z_]+\}\}", out)
    if left:
        sys.exit(f"internal error: unfilled placeholders {sorted(set(left))}")
    Path(args.out).write_text(out, encoding="utf-8")
    print(f"Wrote {args.out}. Check it with:  lean {args.out}   (about 13 minutes; no output = success)")


if __name__ == "__main__":
    main()
