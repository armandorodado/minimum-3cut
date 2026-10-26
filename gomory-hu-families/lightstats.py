"""Statistics of the light cross-free family L (cuts lighter than the first crossing pair)."""
import json, sys
import numpy as np
from families import Inst, fam_NI
from cutlib import edge_connectivity

def main():
    bank = json.load(open("bank.json")) + json.load(open("lpbank.json"))
    rat, frac, hit_part, worst_part = [], [], 0, 0
    for b in bank:
        I = Inst(b["n"], [tuple(e) for e in b["E"]])
        lam = edge_connectivity(I.n, I.d)
        fam = fam_NI(I)
        # tau*: weight of the last cut added (the first crossing one)
        tau = max(I.d[X] for X in fam)
        rat.append(tau / lam)
        frac.append(len(fam) / 2 / (2 * I.n - 3))
        # lightest optimal part relative to lambda
        lp = min(I.d[p] for P in I.optima for p in P)
        worst_part = max(worst_part, lp / lam)
        hit_part += I.hits(fam)
    print(f"instances {len(bank)}; light family hits {hit_part}")
    print(f"tau*/lambda: min {min(rat):.3f}, median {np.median(rat):.3f}, max {max(rat):.3f}")
    print(f"|L| / (2n-3) (bipartitions): median {np.median(frac):.2f}, max {max(frac):.2f}")
    print(f"lightest optimal part / lambda: max {worst_part:.3f}")

main()
