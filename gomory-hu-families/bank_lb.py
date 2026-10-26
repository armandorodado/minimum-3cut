"""Add noisy dense three-cluster graphs in which Gomory-Hu sides fail (kind 'lb')."""
import itertools, json
import numpy as np
from bank import gh_fails, all_hard

def main(target=150, seed=9):
    rng = np.random.default_rng(seed)
    bank = json.load(open("bank.json"))
    got = tries = 0
    while got < target and tries < 3000:
        tries += 1
        sizes = rng.integers(3, 6, 3)
        if sizes.sum() > 12:
            continue
        n = int(sizes.sum()); m = sizes.mean()
        lab = np.repeat(np.arange(3), sizes); rng.shuffle(lab)
        beta = rng.uniform(0.5, 0.7) / m
        E = []
        for u, v in itertools.combinations(range(n), 2):
            if lab[u] == lab[v]:
                w = rng.uniform(0.85, 1.15)
            else:
                w = beta * rng.uniform(0.6, 1.4)
            E.append((u, v, float(w)))
        if all_hard(n, E)[0] and gh_fails(n, E):
            bank.append(dict(kind="lb", n=n, E=E)); got += 1
    print(f"lb: {got} from {tries}")
    json.dump(bank, open("bank.json", "w"))

if __name__ == "__main__":
    main()
