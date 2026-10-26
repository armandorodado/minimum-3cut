/-!
# Machine-checked verification of Theorem 9

The paper's Theorem 9: there is a weighted graph on 7 vertices with a unique
Gomory–Hu (cut) tree `T` and a unique minimum 3-partition, such that no part of
the optimum is a side of `T`, and every 3-partition having a side of `T` as a
part is strictly heavier than the optimum (so Kapoor's value `F(T)` exceeds OPT).

Weights are the six-decimal values printed in the paper, multiplied by `10^6`,
so all arithmetic is on natural numbers. Every statement is a bounded,
decidable proposition proved by `decide +kernel`: the Lean kernel itself
evaluates it. No `native_decide`, no axioms beyond Lean's core.

Vertex numbering: 0 = s, 1 = u₀, 2 = ℓ₀, 3 = ℓ₁, 4 = ℓ₂, 5 = c₀, 6 = c₁.
A vertex set is a bitmask `S < 128`; vertex `i` is in `S` iff bit `i` is set.
A labelling `c < 3^7` assigns vertex `i` the label `c / 3^i % 3`.
-/

set_option maxHeartbeats 0

namespace Theorem9

/-- The 13 weighted edges `(u, v, w)`, weights in units of `10^-6`. -/
def E : List (Nat × Nat × Nat) :=
  [(5,6,337164), (5,2,166989), (6,2,35652), (3,2,221789), (3,4,194170),
   (4,5,110311), (4,2,206713), (0,5,35930), (0,3,210285), (0,4,111054),
   (0,1,364863), (1,5,35173), (1,6,327062)]

/-- Membership of vertex `i` in the vertex set encoded by `S` (bit `i` of `S`).
Written with primitive `Nat` operations, which the kernel evaluates natively. -/
def mem (S i : Nat) : Bool := Nat.beq (Nat.land (Nat.shiftRight S i) 1) 1

/-- Cut weight `d(S)`: total weight of the edges with exactly one end in `S`. -/
def d (S : Nat) : Nat :=
  E.foldl (fun acc e => cond (xor (mem S e.1) (mem S e.2.1)) (Nat.add acc e.2.2) acc) 0

/-! ## Edge connectivity -/

def lam : Nat := 622248

/-- `λ = 0.622248`: every nonempty proper vertex set has cut weight at least
`lam`, and `{ℓ₂}` (bitmask 16) attains it. -/
theorem edge_connectivity :
    (∀ S, S < 128 → 0 < S → S < 127 → lam ≤ d S) ∧ d 16 = lam := by
  decide +kernel

/-! ## Minimum 3-partition -/

def lab (c i : Nat) : Nat := c / 3 ^ i % 3

/-- `c` uses all three labels, i.e. is a 3-partition. -/
def isPart (c : Nat) : Bool :=
  (List.range 7).any (lab c · == 0) && (List.range 7).any (lab c · == 1) &&
  (List.range 7).any (lab c · == 2)

/-- Weight of the 3-partition encoded by `c`. -/
def W (c : Nat) : Nat :=
  E.foldl (fun acc e => if lab c e.1 != lab c e.2.1 then acc + e.2.2 else acc) 0

/-- Two labellings induce the same partition. -/
def sameParts (c c' : Nat) : Bool :=
  (List.range 7).all fun i => (List.range 7).all fun j =>
    (lab c i == lab c j) == (lab c' i == lab c' j)

/-- The optimum `({s,u₀}, {ℓ₀,ℓ₁,ℓ₂}, {c₀,c₁})`:
labels 0,0,1,1,1,2,2, i.e. `9 + 27 + 81 + 2·243 + 2·729 = 2061`. -/
def copt : Nat := 2061

def OPT : Nat := 1032456

theorem copt_spec : isPart copt = true ∧ W copt = OPT := by decide +kernel

/-- `OPT = 1.032456` is the minimum weight of a 3-partition. -/
theorem optimal : ∀ c, c < 3 ^ 7 → isPart c = true → OPT ≤ W c := by
  decide +kernel

/-- The optimum is unique (as a partition). -/
theorem optimum_unique :
    ∀ c, c < 3 ^ 7 → isPart c = true → W c = OPT → sameParts c copt = true := by
  decide +kernel

/-! ## Hardness: all three pair weights are below `λ` -/

/-- Weight of the edges joining vertex sets `X` and `Y` (disjoint). -/
def pairW (X Y : Nat) : Nat :=
  E.foldl (fun acc e =>
    if (mem X e.1 && mem Y e.2.1) || (mem Y e.1 && mem X e.2.1) then acc + e.2.2
    else acc) 0

/-- Parts of the optimum as bitmasks: `{s,u₀} = 3`, `{ℓ₀,ℓ₁,ℓ₂} = 28`,
`{c₀,c₁} = 96`. -/
theorem hard :
    pairW 3 28 = 321339 ∧ pairW 3 96 = 398165 ∧ pairW 28 96 = 312952 ∧
    pairW 3 28 < lam ∧ pairW 3 96 < lam ∧ pairW 28 96 < lam := by
  decide +kernel

/-! ## Gomory–Hu trees as parent lists rooted at `s`

A spanning tree on `{0,…,6}` rooted at `0` is given by a parent list
`P = [0, p₁, …, p₆]`, `pᵢ` the parent of vertex `i`, such that following parents
from any vertex reaches `0`. Every spanning tree arises this way (root it at `s`),
so quantifying over all `7^6` choices of `p₁, …, p₆` covers all spanning trees. -/

def pget (P : List Nat) (j : Nat) : Nat := P.getD j 0

/-- Follow parents from `j` for at most `k` steps. -/
def upP (P : List Nat) : Nat → Nat → Nat
  | 0, j => j
  | k + 1, j => cond (Nat.beq j 0) 0 (upP P k (pget P j))

/-- Every vertex reaches the root within 6 steps, so the edges `{i, pᵢ}`
form a spanning tree. -/
def treeP (P : List Nat) : Bool :=
  Nat.beq (upP P 6 1) 0 && Nat.beq (upP P 6 2) 0 && Nat.beq (upP P 6 3) 0 &&
  Nat.beq (upP P 6 4) 0 && Nat.beq (upP P 6 5) 0 && Nat.beq (upP P 6 6) 0

/-- Walking up from `j` (at most `k` steps) passes through `i`. -/
def walk (P : List Nat) (i : Nat) : Nat → Nat → Bool
  | 0, j => Nat.beq j i
  | k + 1, j => Nat.beq j i || (!(Nat.beq j 0) && walk P i k (pget P j))

/-- The side of tree edge `{i, pᵢ}` containing `i`: the subtree of `i`, as a bitmask. -/
def subP (P : List Nat) (i : Nat) : Nat :=
  [(0, 1), (1, 2), (2, 4), (3, 8), (4, 16), (5, 32), (6, 64)].foldl
    (fun m jb => cond (walk P i 6 jb.1) (Nat.add m jb.2) m) 0

/-- Pairwise connectivities `λ(x,y)`, listed row by row. -/
def lamTab : List Nat :=
  [0, 713745, 631143, 626244, 622248, 685567, 699878,
   713745, 0, 631143, 626244, 622248, 685567, 699878,
   631143, 631143, 0, 626244, 622248, 631143, 631143,
   626244, 626244, 626244, 0, 622248, 626244, 626244,
   622248, 622248, 622248, 622248, 0, 622248, 622248,
   685567, 685567, 631143, 626244, 622248, 0, 685567,
   699878, 699878, 631143, 626244, 622248, 685567, 0]

def lamxy (x y : Nat) : Nat := lamTab.getD (7 * x + y) 0

/-- Least weight of a cut separating `x` from `y`, by direct minimisation
over all 128 vertex sets (the start value exceeds the total edge weight). -/
def lamC (x y : Nat) : Nat :=
  (List.range 128).foldl (fun m S => if mem S x != mem S y then min m (d S) else m) 10000000

/-- `lamTab` is correct: each entry is the minimum weight of an `x`–`y` cut. -/
theorem lamTab_correct :
    ∀ x, x < 7 → ∀ y, y < 7 → x ≠ y → lamxy x y = lamC x y := by
  decide +kernel

/-- Gomory–Hu (cut) tree: every tree edge `{i, pᵢ}` has a fundamental side
whose cut weight equals `λ(i, pᵢ)`, i.e. is a minimum-weight `i`–`pᵢ` cut. -/
def cutTreeP (P : List Nat) : Bool :=
  treeP P && [1, 2, 3, 4, 5, 6].all fun i => Nat.beq (d (subP P i)) (lamxy i (pget P i))

/-- The tree of the paper, the caterpillar with edges s–u₀, s–ℓ₀, s–ℓ₁, s–ℓ₂,
u₀–c₀, u₀–c₁: parents of `u₀, ℓ₀, ℓ₁, ℓ₂` are `s`, parents of `c₀, c₁` are `u₀`. -/
def PT : List Nat := [0, 0, 0, 0, 0, 1, 1]

/-- `T` is a Gomory–Hu cut tree, and its fundamental sides
`{u₀,c₀,c₁}, {ℓ₀}, {ℓ₁}, {ℓ₂}, {c₀}, {c₁}` have the stated weights. -/
theorem T_is_cut_tree :
    cutTreeP PT = true ∧
    (subP PT 1, subP PT 2, subP PT 3, subP PT 4, subP PT 5, subP PT 6) = (98, 4, 8, 16, 32, 64) ∧
    (d 98, d 4, d 8, d 16, d 32, d 64) =
      (713745, 631143, 626244, 622248, 685567, 699878) := by
  decide +kernel

/-- `allN n f` checks `f k` for every `k < n`, by structural recursion. -/
def allN : Nat → (Nat → Bool) → Bool
  | 0, _ => true
  | n + 1, f => f n && allN n f

theorem allN_spec : ∀ (n : Nat) (f : Nat → Bool), allN n f = true → ∀ k, k < n → f k = true
  | 0, _, _, k, hk => absurd hk (Nat.not_lt_zero k)
  | n + 1, f, h, k, hk => by
    simp only [allN, Bool.and_eq_true] at h
    by_cases hkn : k = n
    · subst hkn; exact h.1
    · exact allN_spec n f h.2 k (by omega)

/-- The exhaustive check behind uniqueness, for parents `p₁ = a`, `p₂ = b` of
`u₀, ℓ₀` fixed and `p₃, …, p₆` ranging over all `7^4` values. -/
def sliceCheck (a b : Nat) : Bool :=
  allN 7 fun p₃ => allN 7 fun p₄ => allN 7 fun p₅ => allN 7 fun p₆ =>
    !(cutTreeP [0, a, b, p₃, p₄, p₅, p₆]) ||
      (Nat.beq a 0 && Nat.beq b 0 && Nat.beq p₃ 0 && Nat.beq p₄ 0 && Nat.beq p₅ 1 && Nat.beq p₆ 1)

/-! The `7^6` parent lists are checked in 49 slices of `7^4`, one declaration
each, so that the kernel's caches stay small. -/

theorem slice_0_0 : sliceCheck 0 0 = true := by decide +kernel
theorem slice_0_1 : sliceCheck 0 1 = true := by decide +kernel
theorem slice_0_2 : sliceCheck 0 2 = true := by decide +kernel
theorem slice_0_3 : sliceCheck 0 3 = true := by decide +kernel
theorem slice_0_4 : sliceCheck 0 4 = true := by decide +kernel
theorem slice_0_5 : sliceCheck 0 5 = true := by decide +kernel
theorem slice_0_6 : sliceCheck 0 6 = true := by decide +kernel
theorem slice_1_0 : sliceCheck 1 0 = true := by decide +kernel
theorem slice_1_1 : sliceCheck 1 1 = true := by decide +kernel
theorem slice_1_2 : sliceCheck 1 2 = true := by decide +kernel
theorem slice_1_3 : sliceCheck 1 3 = true := by decide +kernel
theorem slice_1_4 : sliceCheck 1 4 = true := by decide +kernel
theorem slice_1_5 : sliceCheck 1 5 = true := by decide +kernel
theorem slice_1_6 : sliceCheck 1 6 = true := by decide +kernel
theorem slice_2_0 : sliceCheck 2 0 = true := by decide +kernel
theorem slice_2_1 : sliceCheck 2 1 = true := by decide +kernel
theorem slice_2_2 : sliceCheck 2 2 = true := by decide +kernel
theorem slice_2_3 : sliceCheck 2 3 = true := by decide +kernel
theorem slice_2_4 : sliceCheck 2 4 = true := by decide +kernel
theorem slice_2_5 : sliceCheck 2 5 = true := by decide +kernel
theorem slice_2_6 : sliceCheck 2 6 = true := by decide +kernel
theorem slice_3_0 : sliceCheck 3 0 = true := by decide +kernel
theorem slice_3_1 : sliceCheck 3 1 = true := by decide +kernel
theorem slice_3_2 : sliceCheck 3 2 = true := by decide +kernel
theorem slice_3_3 : sliceCheck 3 3 = true := by decide +kernel
theorem slice_3_4 : sliceCheck 3 4 = true := by decide +kernel
theorem slice_3_5 : sliceCheck 3 5 = true := by decide +kernel
theorem slice_3_6 : sliceCheck 3 6 = true := by decide +kernel
theorem slice_4_0 : sliceCheck 4 0 = true := by decide +kernel
theorem slice_4_1 : sliceCheck 4 1 = true := by decide +kernel
theorem slice_4_2 : sliceCheck 4 2 = true := by decide +kernel
theorem slice_4_3 : sliceCheck 4 3 = true := by decide +kernel
theorem slice_4_4 : sliceCheck 4 4 = true := by decide +kernel
theorem slice_4_5 : sliceCheck 4 5 = true := by decide +kernel
theorem slice_4_6 : sliceCheck 4 6 = true := by decide +kernel
theorem slice_5_0 : sliceCheck 5 0 = true := by decide +kernel
theorem slice_5_1 : sliceCheck 5 1 = true := by decide +kernel
theorem slice_5_2 : sliceCheck 5 2 = true := by decide +kernel
theorem slice_5_3 : sliceCheck 5 3 = true := by decide +kernel
theorem slice_5_4 : sliceCheck 5 4 = true := by decide +kernel
theorem slice_5_5 : sliceCheck 5 5 = true := by decide +kernel
theorem slice_5_6 : sliceCheck 5 6 = true := by decide +kernel
theorem slice_6_0 : sliceCheck 6 0 = true := by decide +kernel
theorem slice_6_1 : sliceCheck 6 1 = true := by decide +kernel
theorem slice_6_2 : sliceCheck 6 2 = true := by decide +kernel
theorem slice_6_3 : sliceCheck 6 3 = true := by decide +kernel
theorem slice_6_4 : sliceCheck 6 4 = true := by decide +kernel
theorem slice_6_5 : sliceCheck 6 5 = true := by decide +kernel
theorem slice_6_6 : sliceCheck 6 6 = true := by decide +kernel

theorem all_slices : ∀ a, a < 7 → ∀ b, b < 7 → sliceCheck a b = true
  | 0, _, b, hb =>
    match b, hb with
    | 0, _ => slice_0_0
    | 1, _ => slice_0_1
    | 2, _ => slice_0_2
    | 3, _ => slice_0_3
    | 4, _ => slice_0_4
    | 5, _ => slice_0_5
    | 6, _ => slice_0_6
    | _ + 7, h => absurd h (by omega)
  | 1, _, b, hb =>
    match b, hb with
    | 0, _ => slice_1_0
    | 1, _ => slice_1_1
    | 2, _ => slice_1_2
    | 3, _ => slice_1_3
    | 4, _ => slice_1_4
    | 5, _ => slice_1_5
    | 6, _ => slice_1_6
    | _ + 7, h => absurd h (by omega)
  | 2, _, b, hb =>
    match b, hb with
    | 0, _ => slice_2_0
    | 1, _ => slice_2_1
    | 2, _ => slice_2_2
    | 3, _ => slice_2_3
    | 4, _ => slice_2_4
    | 5, _ => slice_2_5
    | 6, _ => slice_2_6
    | _ + 7, h => absurd h (by omega)
  | 3, _, b, hb =>
    match b, hb with
    | 0, _ => slice_3_0
    | 1, _ => slice_3_1
    | 2, _ => slice_3_2
    | 3, _ => slice_3_3
    | 4, _ => slice_3_4
    | 5, _ => slice_3_5
    | 6, _ => slice_3_6
    | _ + 7, h => absurd h (by omega)
  | 4, _, b, hb =>
    match b, hb with
    | 0, _ => slice_4_0
    | 1, _ => slice_4_1
    | 2, _ => slice_4_2
    | 3, _ => slice_4_3
    | 4, _ => slice_4_4
    | 5, _ => slice_4_5
    | 6, _ => slice_4_6
    | _ + 7, h => absurd h (by omega)
  | 5, _, b, hb =>
    match b, hb with
    | 0, _ => slice_5_0
    | 1, _ => slice_5_1
    | 2, _ => slice_5_2
    | 3, _ => slice_5_3
    | 4, _ => slice_5_4
    | 5, _ => slice_5_5
    | 6, _ => slice_5_6
    | _ + 7, h => absurd h (by omega)
  | 6, _, b, hb =>
    match b, hb with
    | 0, _ => slice_6_0
    | 1, _ => slice_6_1
    | 2, _ => slice_6_2
    | 3, _ => slice_6_3
    | 4, _ => slice_6_4
    | 5, _ => slice_6_5
    | 6, _ => slice_6_6
    | _ + 7, h => absurd h (by omega)
  | _ + 7, h, _, _ => absurd h (by omega)

/-- Uniqueness of the Gomory–Hu tree: every cut tree on the seven vertices,
rooted at `s`, has the same parents as `T`, hence the same edges. -/
theorem cut_tree_unique (p₁ p₂ p₃ p₄ p₅ p₆ : Nat)
    (h₁ : p₁ < 7) (h₂ : p₂ < 7) (h₃ : p₃ < 7) (h₄ : p₄ < 7) (h₅ : p₅ < 7) (h₆ : p₆ < 7)
    (hc : cutTreeP [0, p₁, p₂, p₃, p₄, p₅, p₆] = true) :
    [0, p₁, p₂, p₃, p₄, p₅, p₆] = PT := by
  have h0 := all_slices p₁ h₁ p₂ h₂
  unfold sliceCheck at h0
  have h3 := allN_spec _ _ h0 p₃ h₃
  have h4 := allN_spec _ _ h3 p₄ h₄
  have h5 := allN_spec _ _ h4 p₅ h₅
  have h6 := allN_spec _ _ h5 p₆ h₆
  simp only [hc, Bool.not_true, Bool.false_or, Bool.and_eq_true] at h6
  obtain ⟨⟨⟨⟨⟨e₁, e₂⟩, e₃⟩, e₄⟩, e₅⟩, e₆⟩ := h6
  rw [Nat.eq_of_beq_eq_true e₁, Nat.eq_of_beq_eq_true e₂, Nat.eq_of_beq_eq_true e₃,
    Nat.eq_of_beq_eq_true e₄, Nat.eq_of_beq_eq_true e₅, Nat.eq_of_beq_eq_true e₆]
  rfl

/-- The minimum-weight cut for each edge of `T` is unique. -/
theorem unique_min_cuts :
    ∀ i, i < 6 → ∀ S, S < 128 → mem S (i + 1) = true → mem S (pget PT (i + 1)) = false →
      d S = d (subP PT (i + 1)) → S = subP PT (i + 1) := by
  decide +kernel

/-! ## Gomory–Hu sides do not suffice -/

/-- Bitmask of the part with label `k` in labelling `c`. -/
def block (c k : Nat) : Nat :=
  (List.range 7).foldl (fun m i => if lab c i == k then m + 2 ^ i else m) 0

/-- `X` is a side of `T`: a fundamental side or its complement. -/
def isSide (X : Nat) : Bool :=
  (List.range 6).any fun k => X == subP PT (k + 1) || X == 127 - subP PT (k + 1)

def hasSidePart (c : Nat) : Bool := (List.range 3).any fun k => isSide (block c k)

def FT : Nat := 1035084

/-- **Theorem 9.** Every 3-partition having a side of `T` as a part weighs at
least `F(T) = 1.035084`, which is attained and exceeds `OPT = 1.032456`.
In particular no part of the optimum is a side of `T`. -/
theorem sides_do_not_suffice :
    (∀ c, c < 3 ^ 7 → isPart c = true → hasSidePart c = true → FT ≤ W c) ∧
    -- attained by `({s}, {u₀,c₀,c₁}, {ℓ₀,ℓ₁,ℓ₂})`, labels 0,1,2,2,2,1,1
    (isPart 1209 = true ∧ hasSidePart 1209 = true ∧ W 1209 = FT) ∧
    OPT < FT ∧ hasSidePart copt = false := by
  decide +kernel

end Theorem9
