# Supplementary material

**When is greedy exact for weighted minimum 3-cut?**
Armando Rodado Amaris, Centre for Quantum Software and Information,
University of Technology Sydney.

This folder has two parts:

- `lean/`: Lean 4 proofs. `GreedyCut.lean` formalizes Theorem 1, Corollaries 2 and 3,
  Proposition 5, Lemmas 6 and 7 and the k = 4 example of Section 6, for all n.
  `Theorem9.lean` proves every claim of Theorem 9 (the 7-vertex graph whose Gomory–Hu
  sides do not suffice), and a generator checks other instances;
- `python/`: scripts that reproduce every computation reported in the paper.

Theorem numbers refer to the paper: Theorem 1 (exactness criterion), Corollaries 2–4,
Proposition 5 (hard optima), Lemmas 6–7 (merge lemmas), Theorem 9 (counterexample),
Theorem 10 (minimum k-cut), and Corollaries 11–12.

## Lean proof (`lean/`)

See `lean/README.md` for details. In brief:

```
cd lean
lean GreedyCut.lean     # Lean 4.15.0 (pinned in lean-toolchain); about 10 s
lean Theorem9.lean      # about 13 min, < 3 GB
```

No output means every theorem was accepted. There is no `native_decide`, no `sorry`, and no
Mathlib; only Lean's standard axioms are used. `Theorem9.lean` works by kernel evaluation
(`decide +kernel`).
To check any other 7-vertex instance and generate its proof, run
`python3 lean_instance.py instance.json -o Instance.lean`.

## Python scripts (`python/`)

Requirements: Python 3.9 or later, numpy, scipy (for Delaunay triangulations and the
linear program) and networkx (for connectivity tests). They were tested with
Python 3.13, numpy 2.5, scipy 1.18 and networkx 3.6:

```
pip install numpy scipy networkx
```

Run each script from inside `python/`, for example `cd python && python3 exp1_greedy.py`.
Each script prints its counts and ends with a `RESULT:` line; the exit status is 0
when every check passes. All random choices use fixed seeds, so reruns give the
same counts.

Every quantity is computed by exhaustive enumeration over vertex subsets and
partitions; no max-flow code is used (see the numerical caveat in Section 7 of
the paper). Gomory–Hu trees are built by the classical contraction procedure from
exhaustively computed minimum-weight cuts, and each one is re-verified as a cut tree
before use. Comparisons use a tolerance of 1e-9 times the total weight. Integer
instances, and `verify_theorem9.py`, are exact.

| Script | Paper result (Section 7 table, unless noted) | Reported counts | Time |
| --- | --- | --- | --- |
| `exp1_greedy.py` | Theorem 1, Corollary 3 (4/3), Corollary 2 (inexact ⇒ all optima hard), Proposition 5 | 1,600 graphs, 1,800 global minimum-weight cuts, 0 violations; 121 inexact graphs, all with hard optima only; 429 hard optima, 0 violations | seconds |
| `exp2_merge_lemma.py` | Lemma 7 | 49 non-trivial merges in 20,000 graphs, 0 violations | < 1 min |
| `exp3_gh_sides.py` | F(T) = OPT on random and structured graphs | 0 of 800 random, 0 of 1,577 structured | seconds |
| `exp4_adversarial.py` | F(T) = OPT under adversarial weight search | 0 of 240 climbs reach F(T) > OPT | about 13 min |
| `exp5_caterpillar.py` | The caterpillar linear program (Section 5) and its perturbations | positive margin from shape (3,2) on; F(T) > OPT in 4 of 72 perturbed graphs, 1 of which is fixed by leaf-neighbour sets (open question 1) | seconds |
| `exp6_kcut.py` | Theorem 10, Corollary 11, and the 5-vertex example (Section 6) | condition holds in 685 graphs (k = 3, 4, 5), 0 violations; bound and factor at 963 cuts, 0 violations; the weaker condition fails in 24 of 600 graphs | seconds |
| `verify_theorem9.py` | Theorem 9: independent exact check of every claim | all claims verified | seconds |

`cutlib.py` holds the shared exact routines: the cut table, λ, global minimum-weight
cuts, 3- and k-partition weights, Gomory–Hu trees with verification, F(T), and the
random graph generators.

`verify_theorem9.py` reads `../lean/theorem9_instance.json`, the same file the Lean
generator uses, scales the weights to integers, and checks the claims with exact
arithmetic. Tree uniqueness is checked over all 7^5 = 16,807 labelled spanning trees,
enumerated by Prüfer codes. It accepts another instance file as an argument.

Expected output for each script is in `logs/`.

## Licence

The code is released under the MIT licence; see `LICENSE`.
