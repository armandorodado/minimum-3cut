# Minimum 3-cut: greedy exactness, Gomory–Hu families and planar instances

Code accompanying research by Armando Rodado Amaris on the weighted minimum 3-cut problem.

| Folder | Contents |
| --- | --- |
| [`greedy-3cut/`](greedy-3cut/) | Supplementary material for *When is greedy exact for weighted minimum 3-cut?* (submitted to Operations Research Letters): Lean 4 proofs and Python scripts reproducing every computation in the paper |
| [`gomory-hu-families/`](gomory-hu-families/) | Follow-up work: no small family of candidate parts can be read off a Gomory–Hu tree; tests of candidate families; single-linkage and Stoer–Wagner experiments; k-cut and planar extensions |
| [`planar-hard-instances/`](planar-hard-instances/) | Hard planar instances: light thetas in the dual, and structure tests for an o(n²) algorithm |

## Lean proofs

`greedy-3cut/lean/` uses Lean 4.15.0 with no Mathlib (`lean-toolchain` pins the version).

- `GreedyCut.lean`: Theorem 1, Corollaries 2–3, Proposition 5, Lemmas 6–7 and the k = 4 example, for all n. Takes about 10 seconds.
- `Theorem9.lean`: every claim of Theorem 9, the 7-vertex counterexample. Takes about 13 minutes and under 3 GB.

```
cd greedy-3cut/lean
lean GreedyCut.lean
lean Theorem9.lean
```

No output means success. There is no `sorry` and no `native_decide`; only Lean's standard axioms are used.

## Python

Requirements: Python 3.9 or later, numpy, scipy and networkx (`pip install numpy scipy networkx`). Each folder's README lists its scripts. Run each script from inside its folder. All computations are exhaustive, with no max-flow code, and the theorem checks use exact arithmetic.

## Licence

MIT; see `LICENSE`.
