"""Many Gomory-Hu-LP instances (sides fail), for stress-testing families. Saves lpbank_<seed>.json."""
import json, sys
import numpy as np
import bank as B

def main(seed, target=150, nmax=10):
    rng = np.random.default_rng(seed)
    out = []; tries = 0
    while len(out) < target and tries < 4000:
        tries += 1
        n = int(rng.integers(7, nmax + 1))
        for E in B.lp_instance(n, rng) or []:
            out.append(dict(kind="lp", n=n, E=E))
    print(f"seed {seed}: {len(out)} instances from {tries} tries")
    json.dump(out, open(f"lpbank_{seed}.json", "w"))

if __name__ == "__main__":
    main(int(sys.argv[1]))
