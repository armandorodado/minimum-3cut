# Lean 4 proofs

| File | Purpose |
| --- | --- |
| `GreedyCut.lean` | Theorem 1, Corollaries 2–3, Proposition 5, Lemmas 6–7 and the k = 4 example, for all n |
| `Theorem9.lean` | The verified proof for the instance of Theorem 9 |
| `lean_instance.py` | Checks any 7-vertex instance and generates its Lean proof |
| `Theorem9.template.lean` | Template used by the generator |
| `theorem9_instance.json` | The paper's instance, in the generator's input format |

## Theorem 1 and its consequences (`GreedyCut.lean`)

Run `lean GreedyCut.lean` (about 10 seconds). The file uses plain Lean 4 core, without Mathlib.

**Setting.**

- Vertices are the numbers 0, …, n−1, and edge weights are any function `wt : Nat → Nat → Nat`.
  This covers rational weights by scaling, and symmetry is not needed.
- Vertex sets are Boolean functions.
- Every weight is counted twice, which avoids halving: `cut X` is 2·d(X), `cw P Q` is 2·w(P,Q),
  and `W2 A B C` is 2·W(A,B,C). The paper's statements are homogeneous, so this changes nothing.

| Lean name | Paper |
| --- | --- |
| `posimodular`, `submodular`, `cut_compl` | cut-function facts used throughout |
| `theorem1` | Theorem 1: a bipartition (Y,Z) of S or V∖S with d(S) + w(Y,Z) ≤ max(d(S) + d(A), W(A,B,C)) |
| `greedy_partition` | the greedy 3-partition is a 3-partition of weight d(S) + w(Y,Z) |
| `cor2a`, `cor2b`, `greedy_exact` | Corollary 2 (a), (b), and exactness of greedy |
| `cor3` | Corollary 3, the 4/3 bound |
| `prop5` | Proposition 5 |
| `lemma6`, `lemma7` | the merge lemmas (Lemma 7 with the Gomory–Hu side property as hypothesis) |
| `example_k4_lambda`, `example_k4` | the 5-vertex example of Section 6, by kernel evaluation |

Theorem 10 (minimum k-cut) is not formalized. Its proof refines a partition by a cut and then merges
pieces to obtain exactly k parts, which needs counting machinery best done with Mathlib.

## Checking the Theorem 9 proof

`Theorem9.lean` machine-checks every claim of Theorem 9 (Gomory–Hu sides do not
suffice) for the 7-vertex instance with the weights printed in the paper,
scaled by 10^6 to natural numbers:

- the weighted edge connectivity is λ = 0.622248;
- the minimum-weight 3-partition is unique, with OPT = 1.032456, and hard
  (all pair weights below λ);
- the connectivity table λ(x,y) is correct;
- T is a Gomory–Hu cut tree, and the only one (over all 7^6 parent lists rooted at s);
- each tree edge has a unique minimum-weight cut;
- every 3-partition with a side of T as a part weighs at least
  F(T) = 1.035084 > OPT, and F(T) is attained.

Proofs are by `decide +kernel` (kernel evaluation) plus short structural proofs.
No `native_decide`, no `sorry`, no extra axioms; plain Lean core, no Mathlib.

1. Install elan (https://lean-lang.org/install/).
2. Put a file `lean-toolchain` in this folder containing `leanprover/lean4:v4.15.0`.
3. Run `lean Theorem9.lean`. It takes about 13 minutes and under 3 GB of memory;
   no output means success.

To confirm no unwanted axioms are used, append
`#print axioms Theorem9.sides_do_not_suffice` and check that
`Lean.ofReduceBool` does not appear.

## Checking another instance

Write the instance as JSON (see `theorem9_instance.json`):

```json
{
  "name": "MyInstance",
  "scale": 1000000,
  "vertices": ["s", "u0", "l0", "l1", "l2", "c0", "c1"],
  "edges": [["s", "u0", "0.364863"], ["u0", "c1", "0.327062"]]
}
```

- `name` becomes the Lean namespace (letters, digits, `_`).
- Exactly 7 vertices; the first is the root of the tree's parent list.
- Weights are decimals; multiplied by `scale` they must be positive integers.

Then run:

```
python3 lean_instance.py my_instance.json                        # report only
python3 lean_instance.py my_instance.json -o MyInstance.lean     # report + Lean file
lean MyInstance.lean
```

The script prints λ, the optimum, the tree, F(T) and an ok/FAIL line per claim.
It writes the Lean file only if every claim holds, since otherwise some theorem
in it would be false and Lean would reject it. Needs Python 3.8+ and
`Theorem9.template.lean` in the same folder.

The size (7 vertices) is fixed in the template; larger instances would need
the enumeration bounds changed and would take much longer to check.
