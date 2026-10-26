/-
  Formal proofs for "When is greedy exact for weighted minimum 3-cut?"

  Plain Lean 4 core (tested with Lean 4.15.0), no Mathlib.

  Setting. Vertices are the natural numbers 0, ..., n-1. Edge weights are given by any function
  `wt : Nat → Nat → Nat` (natural numbers; rational weights reduce to this by scaling, and the
  statements are homogeneous). Vertex sets are functions `Nat → Bool`; only their values below n
  matter.

  To avoid halving, every weight is counted twice:
    cut X     = Σ_{u,v<n} [X u ≠ X v] · wt u v                 (= d(X) for symmetric weights, doubled)
    cw P Q    = Σ_{u,v<n} [(P u ∧ Q v) ∨ (Q u ∧ P v)] · wt u v   (= w(P,Q) for disjoint P,Q, doubled)
    W2 A B C  = cw A B + cw A C + cw B C                         (= W(A,B,C), doubled)
  All statements in the paper are homogeneous of degree one in the weights, so doubling changes
  nothing. Symmetry of `wt` is not needed.

  Formalized here:
    * cut-function facts: complement symmetry, submodularity, posimodularity (pointwise);
    * Theorem 1 (`theorem1`): for every 3-partition (A,B,C) and every global minimum cut S there is
      a bipartition (Y,Z) of S or of V∖S with  d(S) + w(Y,Z) ≤ max(d(S) + d(A), W(A,B,C));
    * the greedy 3-partition really is a 3-partition of the stated weight (`greedy_partition`);
    * Corollary 2(a), 2(b) (`cor2a`, `cor2b`) and Corollary 3, the 4/3 bound (`cor3`);
    * Proposition 5 (`prop5`);
    * the merge lemmas, Lemma 6 (`lemma6`) and Lemma 7 (`lemma7`);
    * the 5-vertex k = 4 example of Section 6 (`example_k4`), by kernel evaluation.
  Theorem 9 is formalized separately in Theorem9.lean.
-/

namespace Greedy3Cut

/-! ## Finite sums over `List.range n` -/

def ind (b : Bool) : Nat := if b then 1 else 0

def lsum : List Nat → (Nat → Nat) → Nat
  | [], _ => 0
  | a :: l, f => f a + lsum l f

theorem lsum_mono (l : List Nat) (f g : Nat → Nat) (h : ∀ a, a ∈ l → f a ≤ g a) :
    lsum l f ≤ lsum l g := by
  induction l with
  | nil => simp [lsum]
  | cons a l ih =>
    simp only [lsum]
    have h1 := h a (by simp)
    have h2 := ih (fun b hb => h b (by simp [hb]))
    omega

theorem lsum_add (l : List Nat) (f g : Nat → Nat) :
    lsum l (fun a => f a + g a) = lsum l f + lsum l g := by
  induction l with
  | nil => simp [lsum]
  | cons a l ih => simp only [lsum, ih]; omega

theorem lsum_congr (l : List Nat) (f g : Nat → Nat) (h : ∀ a, a ∈ l → f a = g a) :
    lsum l f = lsum l g := by
  have h1 := lsum_mono l f g (fun a ha => Nat.le_of_eq (h a ha))
  have h2 := lsum_mono l g f (fun a ha => Nat.le_of_eq (h a ha).symm)
  omega

section Graph

variable (n : Nat) (wt : Nat → Nat → Nat)

/-- Double sum over ordered pairs of vertices. -/
def D (f : Nat → Nat → Nat) : Nat :=
  lsum (List.range n) (fun u => lsum (List.range n) (fun v => f u v))

theorem D_mono (f g : Nat → Nat → Nat) (h : ∀ u v, u < n → v < n → f u v ≤ g u v) :
    D n f ≤ D n g := by
  unfold D
  apply lsum_mono
  intro u hu
  apply lsum_mono
  intro v hv
  exact h u v (List.mem_range.mp hu) (List.mem_range.mp hv)

theorem D_add (f g : Nat → Nat → Nat) :
    D n (fun u v => f u v + g u v) = D n f + D n g := by
  unfold D
  rw [← lsum_add]
  apply lsum_congr
  intro u _
  exact lsum_add _ _ _

theorem D_congr (f g : Nat → Nat → Nat) (h : ∀ u v, u < n → v < n → f u v = g u v) :
    D n f = D n g := by
  have h1 := D_mono n f g (fun u v hu hv => Nat.le_of_eq (h u v hu hv))
  have h2 := D_mono n g f (fun u v hu hv => Nat.le_of_eq (h u v hu hv).symm)
  omega

/-! ## Cut function and crossing weight (both doubled) -/

def cut (X : Nat → Bool) : Nat := D n (fun u v => ind (X u != X v) * wt u v)

def cw (P Q : Nat → Bool) : Nat :=
  D n (fun u v => ind ((P u && Q v) || (Q u && P v)) * wt u v)

def W2 (A B C : Nat → Bool) : Nat := cw n wt A B + cw n wt A C + cw n wt B C

def compl (X : Nat → Bool) : Nat → Bool := fun u => !X u
def inter (X Y : Nat → Bool) : Nat → Bool := fun u => X u && Y u
def union (X Y : Nat → Bool) : Nat → Bool := fun u => X u || Y u
def diff (X Y : Nat → Bool) : Nat → Bool := fun u => X u && !Y u

/-- X has an element below n. -/
def Ne (X : Nat → Bool) : Prop := ∃ u, u < n ∧ X u = true
/-- X ⊆ Y below n. -/
def Sub (X Y : Nat → Bool) : Prop := ∀ u, u < n → X u = true → Y u = true
/-- X is a nonempty proper subset of {0..n-1}. -/
def Proper (X : Nat → Bool) : Prop := Ne n X ∧ Ne n (compl X)
/-- S is a global minimum-weight cut. -/
def IsMinCut (S : Nat → Bool) : Prop := Proper n S ∧ ∀ X, Proper n X → cut n wt S ≤ cut n wt X
/-- (A,B,C) is a 3-partition of {0..n-1}. -/
def IsPart3 (A B C : Nat → Bool) : Prop :=
  (∀ u, u < n → (A u && !B u && !C u) || (!A u && B u && !C u) || (!A u && !B u && C u)) ∧
  Ne n A ∧ Ne n B ∧ Ne n C
/-- (Y,Z) is a bipartition of U into two nonempty sets. -/
def IsBip (U Y Z : Nat → Bool) : Prop :=
  (∀ u, u < n → (Y u || Z u) = U u ∧ (Y u && Z u) = false) ∧ Ne n Y ∧ Ne n Z

/-! ### Pointwise Boolean facts -/

theorem pt_compl (a b : Bool) (w : Nat) : ind ((!a) != (!b)) * w = ind (a != b) * w := by
  cases a <;> cases b <;> rfl

theorem pt_posi (a b c d : Bool) (w : Nat) :
    ind ((a && !c) != (b && !d)) * w + ind ((c && !a) != (d && !b)) * w
      ≤ ind (a != b) * w + ind (c != d) * w := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp [ind] <;> omega

theorem pt_sub (a b c d : Bool) (w : Nat) :
    ind ((a && c) != (b && d)) * w + ind ((a || c) != (b || d)) * w
      ≤ ind (a != b) * w + ind (c != d) * w := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp [ind] <;> omega

theorem pt_cw_le (p q x p' q' x' : Bool) (w : Nat)
    (h1 : p = true → x = true) (h2 : q = true → x = false)
    (h3 : p' = true → x' = true) (h4 : q' = true → x' = false) :
    ind ((p && q') || (q && p')) * w ≤ ind (x != x') * w := by
  have hb : ind ((p && q') || (q && p')) ≤ ind (x != x') := by
    revert h1 h2 h3 h4
    cases p <;> cases q <;> cases x <;> cases p' <;> cases q' <;> cases x' <;> decide
  exact Nat.mul_le_mul_right w hb

theorem pt_part (a b c a' b' c' : Bool) (w : Nat)
    (h : ((a && !b && !c) || (!a && b && !c) || (!a && !b && c)) = true)
    (h' : ((a' && !b' && !c') || (!a' && b' && !c') || (!a' && !b' && c')) = true) :
    ind (a != a') * w = ind ((a && b') || (b && a')) * w + ind ((a && c') || (c && a')) * w := by
  cases a <;> cases b <;> cases c <;> cases a' <;> cases b' <;> cases c' <;> simp_all [ind]

theorem pt_cw_comm (p q p' q' : Bool) (w : Nat) :
    ind ((p && q') || (q && p')) * w = ind ((q && p') || (p && q')) * w := by
  cases p <;> cases q <;> cases p' <;> cases q' <;> rfl

/-! ### Cut-function lemmas -/

theorem cut_compl (X : Nat → Bool) : cut n wt (compl X) = cut n wt X := by
  unfold cut compl
  apply D_congr
  intro u v _ _
  exact pt_compl _ _ _

theorem posimodular (X Y : Nat → Bool) :
    cut n wt (diff X Y) + cut n wt (diff Y X) ≤ cut n wt X + cut n wt Y := by
  unfold cut diff
  rw [← D_add, ← D_add]
  apply D_mono
  intro u v _ _
  exact pt_posi _ _ _ _ _

theorem submodular (X Y : Nat → Bool) :
    cut n wt (inter X Y) + cut n wt (union X Y) ≤ cut n wt X + cut n wt Y := by
  unfold cut inter union
  rw [← D_add, ← D_add]
  apply D_mono
  intro u v _ _
  exact pt_sub _ _ _ _ _

/-- If P ⊆ X and Q ⊆ V∖X then w(P,Q) ≤ d(X). -/
theorem cw_le_cut (P Q X : Nat → Bool) (hP : Sub n P X) (hQ : ∀ u, u < n → Q u = true → X u = false) :
    cw n wt P Q ≤ cut n wt X := by
  unfold cw cut
  apply D_mono
  intro u v hu hv
  exact pt_cw_le _ _ _ _ _ _ _ (hP u hu) (hQ u hu) (hP v hv) (hQ v hv)

/-- For a 3-partition, d(A) = w(A,B) + w(A,C). -/
theorem cut_part (A B C : Nat → Bool) (h : ∀ u, u < n →
      ((A u && !B u && !C u) || (!A u && B u && !C u) || (!A u && !B u && C u)) = true) :
    cut n wt A = cw n wt A B + cw n wt A C := by
  unfold cut cw
  rw [← D_add]
  apply D_congr
  intro u v hu hv
  exact pt_part _ _ _ _ _ _ _ (h u hu) (h v hv)

theorem cw_comm (P Q : Nat → Bool) : cw n wt P Q = cw n wt Q P := by
  unfold cw
  apply D_congr
  intro u v _ _
  exact pt_cw_comm _ _ _ _ _

/-- Twice W(A,B,C) is the sum of the three part cuts. -/
theorem two_W2 (A B C : Nat → Bool) (h : IsPart3 n A B C) :
    2 * W2 n wt A B C = cut n wt A + cut n wt B + cut n wt C := by
  have hA := cut_part n wt A B C h.1
  have hB := cut_part n wt B A C (fun u hu => by
    have := h.1 u hu; revert this; cases A u <;> cases B u <;> cases C u <;> decide)
  have hC := cut_part n wt C A B (fun u hu => by
    have := h.1 u hu; revert this; cases A u <;> cases B u <;> cases C u <;> decide)
  have e1 := cw_comm n wt B A
  have e2 := cw_comm n wt C A
  have e3 := cw_comm n wt C B
  unfold W2
  omega

/-! ### Small facts about the case analysis -/

theorem not_sub_ne (X Y : Nat → Bool) (h : ¬ Sub n X Y) : ∃ u, u < n ∧ X u = true ∧ Y u = false := by
  apply Classical.byContradiction
  intro hc
  apply h
  intro u hu hx
  cases hy : Y u
  · exact absurd ⟨u, hu, hx, hy⟩ hc
  · rfl

theorem part_proper_A (A B C : Nat → Bool) (h : IsPart3 n A B C) : Proper n A := by
  refine ⟨h.2.1, ?_⟩
  obtain ⟨b, hb, hbB⟩ := h.2.2.1
  refine ⟨b, hb, ?_⟩
  have := h.1 b hb
  unfold compl
  revert this; rw [hbB]; cases A b <;> cases C b <;> decide

theorem part_perm1 (A B C : Nat → Bool) (h : IsPart3 n A B C) : IsPart3 n B A C := by
  refine ⟨fun u hu => ?_, h.2.2.1, h.2.1, h.2.2.2⟩
  have := h.1 u hu; revert this; cases A u <;> cases B u <;> cases C u <;> decide

theorem part_perm2 (A B C : Nat → Bool) (h : IsPart3 n A B C) : IsPart3 n C A B := by
  refine ⟨fun u hu => ?_, h.2.2.2, h.2.1, h.2.2.1⟩
  have := h.1 u hu; revert this; cases A u <;> cases B u <;> cases C u <;> decide

theorem compl_compl (X : Nat → Bool) : compl (compl X) = X := by
  funext u; unfold compl; cases X u <;> rfl

theorem minCut_compl (S : Nat → Bool) (hS : IsMinCut n wt S) : IsMinCut n wt (compl S) := by
  refine ⟨⟨hS.1.2, ?_⟩, fun X hX => ?_⟩
  · rw [compl_compl]; exact hS.1.1
  · rw [cut_compl]; exact hS.2 X hX

/-! ## Theorem 1 -/

/-- The core case analysis, for a minimum cut S such that A ⊆ S, or S ⊆ A, or A and S cross. -/
theorem theorem1_core (A B C S : Nat → Bool) (hP : IsPart3 n A B C) (hS : IsMinCut n wt S)
    (hcase : Sub n A S ∨ Sub n S A ∨
      (¬ Sub n A S ∧ ¬ Sub n S A ∧ (∃ u, u < n ∧ A u = true ∧ S u = true) ∧
        (∃ u, u < n ∧ A u = false ∧ S u = false))) :
    ∃ U Y Z, (U = S ∨ U = compl S) ∧ IsBip n U Y Z ∧
      cut n wt S + cw n wt Y Z ≤ max (cut n wt S + cut n wt A) (W2 n wt A B C) := by
  have hpart := hP.1
  have hAcut := cut_part n wt A B C hpart
  rcases hcase with hAS | hSA | ⟨hnAS, hnSA, ⟨x, hx, hxA, hxS⟩, ⟨y, hy, hyA, hyS⟩⟩
  · -- A ⊆ S
    by_cases hSA : Sub n S A
    · -- (ii) A = S: split V∖S into B and C
      refine ⟨compl S, B, C, Or.inr rfl, ⟨fun u hu => ?_, hP.2.2.1, hP.2.2.2⟩, ?_⟩
      · have h1 := hpart u hu
        have h2 := hAS u hu
        have h3 := hSA u hu
        unfold compl
        revert h1 h2 h3; cases A u <;> cases B u <;> cases C u <;> cases S u <;> decide
      · have hSAeq : cut n wt S = cut n wt A := by
          unfold cut
          apply D_congr
          intro u v hu hv
          have e1 : S u = A u := by
            have := hAS u hu; have := hSA u hu
            cases hA : A u <;> cases hS' : S u <;> simp_all
          have e2 : S v = A v := by
            have := hAS v hv; have := hSA v hv
            cases hA : A v <;> cases hS' : S v <;> simp_all
          rw [e1, e2]
        unfold W2
        omega
    · -- (i) A ⊊ S: split S into A and S∖A
      obtain ⟨z, hz, hzS, hzA⟩ := not_sub_ne n S A hSA
      refine ⟨S, A, diff S A, Or.inl rfl, ⟨fun u hu => ?_, hP.2.1, ⟨z, hz, ?_⟩⟩, ?_⟩
      · have h2 := hAS u hu
        unfold diff
        revert h2; cases A u <;> cases S u <;> decide
      · unfold diff; rw [hzS, hzA]; rfl
      · have : cw n wt A (diff S A) ≤ cut n wt A :=
          cw_le_cut n wt A (diff S A) A (fun u _ h => h) (fun u _ h => by
            unfold diff at h; revert h; cases S u <;> cases A u <;> decide)
        omega
  · -- (iii) S ⊆ A, A ⊄ S: split V∖S into A∖S and B ∪ C
    by_cases hAS : Sub n A S
    · -- then A = S, handled as case (ii) by symmetry of the argument
      refine ⟨compl S, B, C, Or.inr rfl, ⟨fun u hu => ?_, hP.2.2.1, hP.2.2.2⟩, ?_⟩
      · have h1 := hpart u hu
        have h2 := hAS u hu
        have h3 := hSA u hu
        unfold compl
        revert h1 h2 h3; cases A u <;> cases B u <;> cases C u <;> cases S u <;> decide
      · have hSAeq : cut n wt S = cut n wt A := by
          unfold cut
          apply D_congr
          intro u v hu hv
          have e1 : S u = A u := by
            have := hAS u hu; have := hSA u hu
            cases hA : A u <;> cases hS' : S u <;> simp_all
          have e2 : S v = A v := by
            have := hAS v hv; have := hSA v hv
            cases hA : A v <;> cases hS' : S v <;> simp_all
          rw [e1, e2]
        unfold W2
        omega
    · obtain ⟨z, hz, hzA, hzS⟩ := not_sub_ne n A S hAS
      obtain ⟨b, hb, hbB⟩ := hP.2.2.1
      refine ⟨compl S, diff A S, union B C, Or.inr rfl,
        ⟨fun u hu => ?_, ⟨z, hz, ?_⟩, ⟨b, hb, ?_⟩⟩, ?_⟩
      · have h1 := hpart u hu
        have h3 := hSA u hu
        unfold diff union compl
        revert h1 h3; cases A u <;> cases B u <;> cases C u <;> cases S u <;> decide
      · unfold diff; rw [hzA, hzS]; rfl
      · unfold union; rw [hbB]; rfl
      · have : cw n wt (diff A S) (union B C) ≤ cut n wt A :=
          cw_le_cut n wt (diff A S) (union B C) A
            (fun u _ h => by unfold diff at h; revert h; cases A u <;> cases S u <;> decide)
            (fun u hu h => by
              have h1 := hpart u hu
              unfold union at h; revert h h1; cases A u <;> cases B u <;> cases C u <;> decide)
        omega
  · -- (iv) A and S cross: split V∖S into A∖S and (V∖S)∖A
    obtain ⟨z, hz, hzA, hzS⟩ := not_sub_ne n A S hnAS
    obtain ⟨t, ht, htS, htA⟩ := not_sub_ne n S A hnSA
    refine ⟨compl S, diff A S, diff (compl S) A, Or.inr rfl,
      ⟨fun u hu => ?_, ⟨z, hz, ?_⟩, ⟨y, hy, ?_⟩⟩, ?_⟩
    · unfold diff compl; cases A u <;> cases S u <;> decide
    · unfold diff; rw [hzA, hzS]; rfl
    · unfold diff compl; rw [hyA, hyS]; rfl
    · have hcw : cw n wt (diff A S) (diff (compl S) A) ≤ cut n wt (diff A S) :=
        cw_le_cut n wt (diff A S) (diff (compl S) A) (diff A S) (fun u _ h => h)
          (fun u _ h => by unfold diff compl at h; unfold diff; revert h; cases A u <;> cases S u <;> decide)
      have hpos := posimodular n wt A S
      -- S∖A is a nonempty proper subset, so d(S∖A) ≥ λ = d(S)
      have hprop : Proper n (diff S A) := by
        refine ⟨⟨t, ht, ?_⟩, ⟨x, hx, ?_⟩⟩
        · unfold diff; rw [htS, htA]; rfl
        · unfold compl diff; rw [hxA, hxS]; rfl
      have hmin := hS.2 _ hprop
      omega

/-- **Theorem 1.** For every 3-partition (A,B,C) and every global minimum-weight cut S there is a
bipartition (Y,Z) of S or of V∖S into nonempty sets with
`d(S) + w(Y,Z) ≤ max (d(S) + d(A)) W(A,B,C)` (all quantities doubled). -/
theorem theorem1 (A B C S : Nat → Bool) (hP : IsPart3 n A B C) (hS : IsMinCut n wt S) :
    ∃ U Y Z, (U = S ∨ U = compl S) ∧ IsBip n U Y Z ∧
      cut n wt S + cw n wt Y Z ≤ max (cut n wt S + cut n wt A) (W2 n wt A B C) := by
  by_cases h1 : Sub n A S ∨ Sub n S A
  · exact theorem1_core n wt A B C S hP hS (h1.elim Or.inl (fun h => Or.inr (Or.inl h)))
  · by_cases h2 : Sub n A (compl S) ∨ Sub n (compl S) A
    · have hS' := minCut_compl n wt S hS
      obtain ⟨U, Y, Z, hU, hB, hle⟩ :=
        theorem1_core n wt A B C (compl S) hP hS' (h2.elim Or.inl (fun h => Or.inr (Or.inl h)))
      refine ⟨U, Y, Z, ?_, hB, ?_⟩
      · rcases hU with h | h
        · exact Or.inr h
        · exact Or.inl (h.trans (compl_compl S))
      · rw [cut_compl] at hle; exact hle
    · have hnAS : ¬ Sub n A S := fun h => h1 (Or.inl h)
      have hnSA : ¬ Sub n S A := fun h => h1 (Or.inr h)
      have hnAc : ¬ Sub n A (compl S) := fun h => h2 (Or.inl h)
      have hncA : ¬ Sub n (compl S) A := fun h => h2 (Or.inr h)
      obtain ⟨x, hx, hxA, hxS⟩ := not_sub_ne n A (compl S) hnAc
      obtain ⟨y, hy, hyS, hyA⟩ := not_sub_ne n (compl S) A hncA
      refine theorem1_core n wt A B C S hP hS (Or.inr (Or.inr ⟨hnAS, hnSA, ⟨x, hx, hxA, ?_⟩, ⟨y, hy, hyA, ?_⟩⟩))
      · unfold compl at hxS; revert hxS; cases S x <;> decide
      · unfold compl at hyS; revert hyS; cases S y <;> decide

/-- The greedy 3-partition (V∖U, Y, Z) is a 3-partition, and its weight is d(S) + w(Y,Z). -/
theorem greedy_partition (S U Y Z : Nat → Bool) (hS : IsMinCut n wt S)
    (hU : U = S ∨ U = compl S) (hB : IsBip n U Y Z) :
    IsPart3 n (compl U) Y Z ∧ W2 n wt (compl U) Y Z = cut n wt S + cw n wt Y Z := by
  have hcU : cut n wt U = cut n wt S := by
    rcases hU with h | h <;> subst h
    · rfl
    · exact cut_compl n wt S
  have hpart : ∀ u, u < n → ((compl U u && !Y u && !Z u) || (!compl U u && Y u && !Z u) ||
      (!compl U u && !Y u && Z u)) = true := by
    intro u hu
    have := hB.1 u hu
    unfold compl
    revert this; cases U u <;> cases Y u <;> cases Z u <;> decide
  have hne : Ne n (compl U) := by
    rcases hU with h | h <;> subst h
    · exact hS.1.2
    · rw [compl_compl]; exact hS.1.1
  refine ⟨⟨hpart, hne, hB.2.1, hB.2.2⟩, ?_⟩
  have := cut_part n wt (compl U) Y Z hpart
  rw [cut_compl] at this
  unfold W2
  omega

/-! ## Corollaries 2 and 3, Proposition 5 -/

/-- **Corollary 2(b).** If w(B,C) ≥ λ for a 3-partition (A,B,C), the greedy 3-partition from any
global minimum cut weighs at most W(A,B,C); so greedy is exact when (A,B,C) is an optimum. -/
theorem cor2b (A B C S : Nat → Bool) (hP : IsPart3 n A B C) (hS : IsMinCut n wt S)
    (hBC : cut n wt S ≤ cw n wt B C) :
    ∃ U Y Z, (U = S ∨ U = compl S) ∧ IsBip n U Y Z ∧
      cut n wt S + cw n wt Y Z ≤ W2 n wt A B C := by
  obtain ⟨U, Y, Z, hU, hB, hle⟩ := theorem1 n wt A B C S hP hS
  have hA := cut_part n wt A B C hP.1
  refine ⟨U, Y, Z, hU, hB, ?_⟩
  unfold W2 at *
  omega

/-- Greedy is exact: under the hypothesis of Corollary 2(b), if (A,B,C) is an optimum then so is
the greedy 3-partition. -/
theorem greedy_exact (A B C S : Nat → Bool) (hP : IsPart3 n A B C) (hS : IsMinCut n wt S)
    (hBC : cut n wt S ≤ cw n wt B C)
    (hopt : ∀ A' B' C', IsPart3 n A' B' C' → W2 n wt A B C ≤ W2 n wt A' B' C') :
    ∃ A' B' C', IsPart3 n A' B' C' ∧ W2 n wt A' B' C' = W2 n wt A B C ∧
      (A' = compl S ∨ A' = S) := by
  obtain ⟨U, Y, Z, hU, hB, hle⟩ := cor2b n wt A B C S hP hS hBC
  obtain ⟨hP', hW⟩ := greedy_partition n wt S U Y Z hS hU hB
  have := hopt _ _ _ hP'
  refine ⟨compl U, Y, Z, hP', by omega, ?_⟩
  rcases hU with h | h <;> subst h
  · exact Or.inl rfl
  · exact Or.inr (compl_compl S)

/-- **Corollary 2(a).** If two parts A, B of a 3-partition are joined by no edge, the greedy bound
W(A,B,C) holds. -/
theorem cor2a (A B C S : Nat → Bool) (hP : IsPart3 n A B C) (hS : IsMinCut n wt S)
    (hAB : cw n wt A B = 0) :
    ∃ U Y Z, (U = S ∨ U = compl S) ∧ IsBip n U Y Z ∧
      cut n wt S + cw n wt Y Z ≤ W2 n wt A B C := by
  -- d(A) = w(A,C) ≥ λ, so apply Corollary 2(b) to the partition (B, A, C) and its pair (A, C)
  have hA := cut_part n wt A B C hP.1
  have hmin := hS.2 A (part_proper_A n A B C hP)
  have hP' := part_perm1 n A B C hP
  obtain ⟨U, Y, Z, hU, hB, hle⟩ := cor2b n wt B A C S hP' hS (by omega)
  refine ⟨U, Y, Z, hU, hB, ?_⟩
  have e := cw_comm n wt B A
  unfold W2 at *
  omega

/-- **Corollary 3** (the 4/3 bound): 3·greedy(S) ≤ 4·W(A,B,C) for every 3-partition. -/
theorem cor3 (A B C S : Nat → Bool) (hP : IsPart3 n A B C) (hS : IsMinCut n wt S) :
    ∃ U Y Z, (U = S ∨ U = compl S) ∧ IsBip n U Y Z ∧
      3 * (cut n wt S + cw n wt Y Z) ≤ 4 * W2 n wt A B C := by
  have hA := cut_part n wt A B C hP.1
  have hPB := part_perm1 n A B C hP
  have hPC := part_perm2 n A B C hP
  have hB := cut_part n wt B A C hPB.1
  have hC := cut_part n wt C A B hPC.1
  have mA := hS.2 A (part_proper_A n A B C hP)
  have mB := hS.2 B (part_proper_A n B A C hPB)
  have mC := hS.2 C (part_proper_A n C A B hPC)
  have e1 := cw_comm n wt B A
  have e2 := cw_comm n wt C A
  have e3 := cw_comm n wt C B
  -- choose the part opposite the heaviest pair
  by_cases h1 : cw n wt A B ≤ cw n wt B C ∧ cw n wt A C ≤ cw n wt B C
  · obtain ⟨U, Y, Z, hU, hb, hle⟩ := theorem1 n wt A B C S hP hS
    refine ⟨U, Y, Z, hU, hb, ?_⟩
    unfold W2 at *
    omega
  · by_cases h2 : cw n wt A B ≤ cw n wt A C
    · -- heaviest pair (A,C): the opposite part is B
      obtain ⟨U, Y, Z, hU, hb, hle⟩ := theorem1 n wt B A C S hPB hS
      refine ⟨U, Y, Z, hU, hb, ?_⟩
      unfold W2 at *
      omega
    · -- heaviest pair (A,B): the opposite part is C
      obtain ⟨U, Y, Z, hU, hb, hle⟩ := theorem1 n wt C A B S hPC hS
      refine ⟨U, Y, Z, hU, hb, ?_⟩
      unfold W2 at *
      omega

/-- **Proposition 5.** For a hard 3-partition (all pair weights below λ = d(S)):
0 < w(X,Y) < λ, λ ≤ d(X) < 2λ, and 3λ/2 ≤ W < 3λ (all doubled). -/
theorem prop5 (A B C S : Nat → Bool) (hP : IsPart3 n A B C) (hS : IsMinCut n wt S)
    (hAB : cw n wt A B < cut n wt S) (hAC : cw n wt A C < cut n wt S) (hBC : cw n wt B C < cut n wt S) :
    0 < cw n wt A B ∧ 0 < cw n wt A C ∧ 0 < cw n wt B C ∧
    cut n wt S ≤ cut n wt A ∧ cut n wt A < 2 * cut n wt S ∧
    cut n wt S ≤ cut n wt B ∧ cut n wt B < 2 * cut n wt S ∧
    cut n wt S ≤ cut n wt C ∧ cut n wt C < 2 * cut n wt S ∧
    3 * cut n wt S ≤ 2 * W2 n wt A B C ∧ W2 n wt A B C < 3 * cut n wt S := by
  have hPB := part_perm1 n A B C hP
  have hPC := part_perm2 n A B C hP
  have hA := cut_part n wt A B C hP.1
  have hB := cut_part n wt B A C hPB.1
  have hC := cut_part n wt C A B hPC.1
  have mA := hS.2 A (part_proper_A n A B C hP)
  have mB := hS.2 B (part_proper_A n B A C hPB)
  have mC := hS.2 C (part_proper_A n C A B hPC)
  have e1 := cw_comm n wt B A
  have e2 := cw_comm n wt C A
  have e3 := cw_comm n wt C B
  unfold W2
  omega

/-! ## The merge lemmas (Lemmas 6 and 7) -/

/-- Core of Lemmas 6 and 7: if a ∈ A ∩ X and every subset of X containing a is at least as
heavy as X, then d(A∪X) + d(B∖X) + d(C∖X) ≤ d(A) + d(B) + d(C). -/
theorem merge_core (A B C X : Nat → Bool) (a : Nat) (ha : a < n) (hP : IsPart3 n A B C)
    (haA : A a = true) (haX : X a = true)
    (hX : ∀ Y, Sub n Y X → Y a = true → cut n wt X ≤ cut n wt Y) :
    cut n wt (union A X) + cut n wt (diff B X) + cut n wt (diff C X)
      ≤ cut n wt A + cut n wt B + cut n wt C := by
  have hBa : B a = false := by
    have := hP.1 a ha; revert this; rw [haA]; cases B a <;> cases C a <;> decide
  have hCa : C a = false := by
    have := hP.1 a ha; revert this; rw [haA]; cases B a <;> cases C a <;> decide
  have s1 := submodular n wt A X
  have s2 := posimodular n wt B X
  have s3 := posimodular n wt C X
  have m1 := hX (inter A X) (fun u _ h => by unfold inter at h; revert h; cases A u <;> cases X u <;> decide)
    (by unfold inter; rw [haA, haX]; rfl)
  have m2 := hX (diff X B) (fun u _ h => by unfold diff at h; revert h; cases X u <;> cases B u <;> decide)
    (by unfold diff; rw [haX, hBa]; rfl)
  have m3 := hX (diff X C) (fun u _ h => by unfold diff at h; revert h; cases X u <;> cases C u <;> decide)
    (by unfold diff; rw [haX, hCa]; rfl)
  omega

/-- The merged triple is a 3-partition when X misses a vertex of B and a vertex of C. -/
theorem merge_partition (A B C X : Nat → Bool) (hP : IsPart3 n A B C)
    (hb : ∃ b, b < n ∧ B b = true ∧ X b = false) (hc : ∃ c, c < n ∧ C c = true ∧ X c = false) :
    IsPart3 n (union A X) (diff B X) (diff C X) := by
  obtain ⟨a, ha, haA⟩ := hP.2.1
  obtain ⟨b, hb, hbB, hbX⟩ := hb
  obtain ⟨c, hc, hcC, hcX⟩ := hc
  refine ⟨fun u hu => ?_, ⟨a, ha, ?_⟩, ⟨b, hb, ?_⟩, ⟨c, hc, ?_⟩⟩
  · have := hP.1 u hu
    unfold union diff
    revert this; cases A u <;> cases B u <;> cases C u <;> cases X u <;> decide
  · unfold union; rw [haA]; rfl
  · unfold diff; rw [hbB, hbX]; rfl
  · unfold diff; rw [hcC, hcX]; rfl

/-- **Lemma 6.** Let (A,B,C) be a 3-partition, a ∈ A, and R a set meeting both B and C and avoiding
a. If X is the a-side of a minimum-weight cut separating a from R, then
(A ∪ X, B ∖ X, C ∖ X) is a 3-partition with W no larger. -/
theorem lemma6 (A B C X R : Nat → Bool) (a : Nat) (ha : a < n) (hP : IsPart3 n A B C)
    (haA : A a = true) (haX : X a = true) (hXR : ∀ u, u < n → R u = true → X u = false)
    (hRB : ∃ b, b < n ∧ B b = true ∧ R b = true) (hRC : ∃ c, c < n ∧ C c = true ∧ R c = true)
    (hmin : ∀ Y, Y a = true → (∀ u, u < n → R u = true → Y u = false) → cut n wt X ≤ cut n wt Y) :
    IsPart3 n (union A X) (diff B X) (diff C X) ∧
      W2 n wt (union A X) (diff B X) (diff C X) ≤ W2 n wt A B C := by
  have hX : ∀ Y, Sub n Y X → Y a = true → cut n wt X ≤ cut n wt Y := by
    intro Y hYX hYa
    apply hmin Y hYa
    intro u hu hR
    have := hXR u hu hR
    cases hY : Y u
    · rfl
    · have := hYX u hu hY; simp_all
  obtain ⟨b, hb, hbB, hbR⟩ := hRB
  obtain ⟨c, hc, hcC, hcR⟩ := hRC
  have hP' := merge_partition n A B C X hP ⟨b, hb, hbB, hXR b hb hbR⟩ ⟨c, hc, hcC, hXR c hc hcR⟩
  refine ⟨hP', ?_⟩
  have h1 := two_W2 n wt _ _ _ hP'
  have h2 := two_W2 n wt _ _ _ hP
  have h3 := merge_core n wt A B C X a ha hP haA haX hX
  omega

/-- **Lemma 7.** If X is a Gomory–Hu side containing s ∈ A (so every subset of X containing s is at
least as heavy as X) and X contains neither all of B nor all of C, then (A ∪ X, B ∖ X, C ∖ X) is a
3-partition with W no larger. -/
theorem lemma7 (A B C X : Nat → Bool) (s : Nat) (hs : s < n) (hP : IsPart3 n A B C)
    (hsA : A s = true) (hsX : X s = true)
    (hGH : ∀ Y, Sub n Y X → Y s = true → cut n wt X ≤ cut n wt Y)
    (hb : ∃ b, b < n ∧ B b = true ∧ X b = false) (hc : ∃ c, c < n ∧ C c = true ∧ X c = false) :
    IsPart3 n (union A X) (diff B X) (diff C X) ∧
      W2 n wt (union A X) (diff B X) (diff C X) ≤ W2 n wt A B C := by
  have hP' := merge_partition n A B C X hP hb hc
  refine ⟨hP', ?_⟩
  have h1 := two_W2 n wt _ _ _ hP'
  have h2 := two_W2 n wt _ _ _ hP
  have h3 := merge_core n wt A B C X s hs hP hsA hsX hGH
  omega

end Graph

/-! ## The k = 4 example of Section 6 (kernel evaluation)

A 4-cycle 0-1-2-3-0 with unit weights and a pendant vertex 4 attached to 0 by weight 2. With
weights counted twice: λ = 2 (doubled: 4) is attained by {4}; the minimum 4-partition has weight 4
(doubled: 8); and every 4-partition having {4} as a part weighs at least 5 (doubled: 10). -/

def exWt : Nat → Nat → Nat
  | 0, 1 => 1 | 1, 0 => 1 | 1, 2 => 1 | 2, 1 => 1 | 2, 3 => 1 | 3, 2 => 1
  | 3, 0 => 1 | 0, 3 => 1 | 0, 4 => 2 | 4, 0 => 2 | _, _ => 0

/-- Doubled weight of the partition given by a labelling (each vertex gets a label < 4). -/
def labWeight (lab : Nat → Nat) : Nat :=
  D 5 (fun u v => ind (lab u != lab v) * exWt u v)

/-- All labellings of 5 vertices with labels 0..3, as lists. -/
def allLabs : List (List Nat) :=
  ((List.range 4).flatMap fun a => (List.range 4).flatMap fun b => (List.range 4).flatMap fun c =>
    (List.range 4).flatMap fun d => (List.range 4).map fun e => [a, b, c, d, e])

def labOf (l : List Nat) : Nat → Nat := fun u => l.getD u 0

def usesAll (l : List Nat) : Bool := (List.range 4).all (fun k => l.contains k)

set_option maxRecDepth 200000 in
/-- Every global minimum cut has doubled weight 4, attained by {4}. -/
theorem example_k4_lambda :
    (List.range 32).all (fun m => m == 0 || m == 31 ||
      decide (4 ≤ cut 5 exWt (fun u => (m >>> u) % 2 == 1))) = true ∧
    cut 5 exWt (fun u => u == 4) = 4 := by
  decide +kernel

set_option maxRecDepth 200000 in
/-- The minimum 4-partition has doubled weight 8 (attained by {0,4},{1},{2},{3}), and every
4-partition with {4} as a part has doubled weight at least 10 (attained by {4},{0,1},{2},{3}),
so R_4({4}) = 5 > 4 = OPT_4. -/
theorem example_k4 :
    allLabs.all (fun l => !usesAll l || decide (8 ≤ labWeight (labOf l))) = true ∧
    labWeight (labOf [0, 1, 2, 3, 0]) = 8 ∧
    allLabs.all (fun l => !usesAll l ||
      !((List.range 4).all fun u => labOf l u != labOf l 4) ||
      decide (10 ≤ labWeight (labOf l))) = true ∧
    labWeight (labOf [0, 0, 1, 2, 3]) = 10 := by
  decide +kernel

end Greedy3Cut
