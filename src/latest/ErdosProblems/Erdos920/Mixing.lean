import Mathlib

/-!
# A finite expander-mixing calculation

This file treats a symmetric finite relation in which every row has the same
size and every two distinct rows have the same intersection size.  The
relation is allowed to have loops.  We record the exact first and second
moments of its restricted degrees, and then the resulting Cauchy--Schwarz
mixing inequality.
-/

namespace Erdos920.Mixing

open scoped BigOperators

noncomputable section

variable {V : Type*} [Fintype V]

/-- The number of `R`-neighbours of `x` which lie in `B`. -/
def restrictedDegree (R : V → V → Prop) [DecidableRel R]
    (B : Finset V) (x : V) : ℕ :=
  (B.filter (R x)).card

/-- The ordered `R`-edge count from `A` to `B`.  A loop in `A ∩ B` is
counted once. -/
def orderedEdges (R : V → V → Prop) [DecidableRel R]
    (A B : Finset V) : ℕ :=
  ∑ x ∈ A, restrictedDegree R B x

lemma sum_restrictedDegree_univ
    (R : V → V → Prop) [DecidableRel R] (d : ℕ)
    (hsymm : ∀ ⦃x y⦄, R x y → R y x)
    (hdegree : ∀ x, (Finset.univ.filter (R x)).card = d)
    (B : Finset V) :
    ∑ x : V, restrictedDegree R B x = d * B.card := by
  classical
  simp_rw [restrictedDegree, Finset.card_filter]
  rw [Finset.sum_comm]
  calc
    (∑ y ∈ B, ∑ x : V, (if R x y then 1 else 0 : ℕ)) =
        ∑ y ∈ B, d := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [← Finset.card_filter]
      have heq : (Finset.univ.filter fun x ↦ R x y) =
          Finset.univ.filter (R y) := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨(fun h ↦ hsymm h), (fun h ↦ hsymm h)⟩
      rw [heq, hdegree]
    _ = d * B.card := by simp [mul_comm]

lemma orderedEdges_univ_left
    (R : V → V → Prop) [DecidableRel R] (d : ℕ)
    (hsymm : ∀ ⦃x y⦄, R x y → R y x)
    (hdegree : ∀ x, (Finset.univ.filter (R x)).card = d)
    (B : Finset V) :
    orderedEdges R Finset.univ B = d * B.card := by
  simpa [orderedEdges] using sum_restrictedDegree_univ R d hsymm hdegree B

omit [Fintype V] in
lemma restrictedDegree_sq
    (R : V → V → Prop) [DecidableRel R] (B : Finset V) (x : V) :
    restrictedDegree R B x ^ 2 =
      ∑ y ∈ B, ∑ z ∈ B, if R x y ∧ R x z then 1 else 0 := by
  classical
  let C := B.filter (R x)
  calc
    restrictedDegree R B x ^ 2 = (C ×ˢ C).card := by
      simp [restrictedDegree, C, pow_two]
    _ = (((B ×ˢ B).filter fun yz ↦ R x yz.1 ∧ R x yz.2)).card := by
      congr 1
      ext yz
      simp only [Finset.mem_product, Finset.mem_filter, C]
      aesop
    _ = ∑ yz ∈ B ×ˢ B, if R x yz.1 ∧ R x yz.2 then 1 else 0 := by
      rw [Finset.card_filter]
    _ = ∑ y ∈ B, ∑ z ∈ B, if R x y ∧ R x z then 1 else 0 := by
      rw [Finset.sum_product]

omit [Fintype V] in
lemma sum_diagonal_offDiagonal [DecidableEq V] (B : Finset V) (d a : ℕ) :
    (∑ y ∈ B, ∑ z ∈ B, if y = z then d else a) =
      d * B.card + a * B.card * (B.card - 1) := by
  classical
  calc
    (∑ y ∈ B, ∑ z ∈ B, if y = z then d else a) =
        ∑ y ∈ B, (d + a * (B.card - 1)) := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [← Finset.sum_erase_add _ _ hy]
      have hoff : (∑ z ∈ B.erase y, if y = z then d else a) =
          a * (B.card - 1) := by
        calc
          (∑ z ∈ B.erase y, if y = z then d else a) =
              ∑ _z ∈ B.erase y, a := by
            apply Finset.sum_congr rfl
            intro z hz
            rw [if_neg]
            exact Ne.symm (Finset.ne_of_mem_erase hz)
          _ = a * (B.card - 1) := by
            simp [Finset.card_erase_of_mem hy, mul_comm]
      rw [hoff, if_pos rfl, add_comm]
    _ = d * B.card + a * B.card * (B.card - 1) := by
      simp
      ring

/-- Exact second moment of the number of neighbours which lie in `B`. -/
lemma sum_restrictedDegree_sq
    (R : V → V → Prop) [DecidableRel R] (d a : ℕ)
    (hsymm : ∀ ⦃x y⦄, R x y → R y x)
    (hdegree : ∀ x, (Finset.univ.filter (R x)).card = d)
    (hcommon : ∀ x y, x ≠ y →
      (Finset.univ.filter fun z ↦ R x z ∧ R y z).card = a)
    (B : Finset V) :
    ∑ x : V, restrictedDegree R B x ^ 2 =
      d * B.card + a * B.card * (B.card - 1) := by
  classical
  simp_rw [restrictedDegree_sq]
  calc
    (∑ x : V, ∑ y ∈ B, ∑ z ∈ B,
        if R x y ∧ R x z then 1 else 0) =
        ∑ y ∈ B, ∑ z ∈ B, ∑ x : V,
          if R x y ∧ R x z then 1 else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y hy
      rw [Finset.sum_comm]
    _ = ∑ y ∈ B, ∑ z ∈ B, if y = z then d else a := by
      apply Finset.sum_congr rfl
      intro y hy
      apply Finset.sum_congr rfl
      intro z hz
      rw [← Finset.card_filter]
      have heq : (Finset.univ.filter fun x ↦ R x y ∧ R x z) =
          Finset.univ.filter fun x ↦ R y x ∧ R z x := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact and_congr
          ⟨(fun h ↦ hsymm h), (fun h ↦ hsymm h)⟩
          ⟨(fun h ↦ hsymm h), (fun h ↦ hsymm h)⟩
      rw [heq]
      by_cases hyz : y = z
      · subst z
        simpa using hdegree y
      · simpa [hyz] using hcommon y z hyz
    _ = d * B.card + a * B.card * (B.card - 1) :=
      sum_diagonal_offDiagonal B d a

/-- The numerator of the centered restricted degree.  Thus, if `N = |V|`,
this is `N * deg_B(x) - d * |B|`.  Avoiding division makes the definition
useful without a nonemptiness assumption on `V`. -/
def scaledCenteredDegree (R : V → V → Prop) [DecidableRel R]
    (d : ℕ) (B : Finset V) (x : V) : ℝ :=
  (Fintype.card V : ℝ) * restrictedDegree R B x -
    (d : ℝ) * B.card

/-- Summing the centered degrees over `A` gives the scaled discrepancy of the
ordered edge count. -/
lemma sum_scaledCenteredDegree
    (R : V → V → Prop) [DecidableRel R] (d : ℕ) (A B : Finset V) :
    ∑ x ∈ A, scaledCenteredDegree R d B x =
      (Fintype.card V : ℝ) * orderedEdges R A B -
        (d : ℝ) * A.card * B.card := by
  classical
  simp only [scaledCenteredDegree, orderedEdges, Nat.cast_sum,
    Finset.sum_sub_distrib, Finset.mul_sum]
  simp
  ring

/-- Finite Cauchy--Schwarz bounds the squared edge discrepancy by the full
second moment of the centered restricted degrees. -/
lemma orderedEdges_deviation_sq_le_card_mul_sum
    (R : V → V → Prop) [DecidableRel R] (d : ℕ) (A B : Finset V) :
    ((Fintype.card V : ℝ) * orderedEdges R A B -
        (d : ℝ) * A.card * B.card) ^ 2 ≤
      (A.card : ℝ) * ∑ x : V, (scaledCenteredDegree R d B x) ^ 2 := by
  classical
  have hc := sq_sum_le_card_mul_sum_sq
    (s := A) (f := fun x ↦ scaledCenteredDegree R d B x)
  have hsub :
      (∑ x ∈ A, (scaledCenteredDegree R d B x) ^ 2) ≤
        ∑ x : V, (scaledCenteredDegree R d B x) ^ 2 := by
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A)
      (fun _ _ _ ↦ sq_nonneg _)
  rw [sum_scaledCenteredDegree] at hc
  exact hc.trans (mul_le_mul_of_nonneg_left hsub (Nat.cast_nonneg A.card))

/-- Exact (unnormalized) variance identity.  It is stated with natural-number
casts around the two combinatorial moments, so it is valid without any
positivity assumptions and without rewriting truncated subtraction. -/
lemma sum_scaledCenteredDegree_sq
    (R : V → V → Prop) [DecidableRel R] (d a : ℕ)
    (hsymm : ∀ ⦃x y⦄, R x y → R y x)
    (hdegree : ∀ x, (Finset.univ.filter (R x)).card = d)
    (hcommon : ∀ x y, x ≠ y →
      (Finset.univ.filter fun z ↦ R x z ∧ R y z).card = a)
    (B : Finset V) :
    ∑ x : V, (scaledCenteredDegree R d B x) ^ 2 =
      (Fintype.card V : ℝ) ^ 2 *
          (d * B.card + a * B.card * (B.card - 1) : ℕ) -
        (Fintype.card V : ℝ) * (d * B.card : ℕ) ^ 2 := by
  classical
  have hfirst :
      (∑ x : V, (restrictedDegree R B x : ℝ)) = (d * B.card : ℕ) := by
    exact_mod_cast sum_restrictedDegree_univ R d hsymm hdegree B
  have hsecond :
      (∑ x : V, (restrictedDegree R B x : ℝ) ^ 2) =
        (d * B.card + a * B.card * (B.card - 1) : ℕ) := by
    exact_mod_cast sum_restrictedDegree_sq R d a hsymm hdegree hcommon B
  calc
    (∑ x : V, (scaledCenteredDegree R d B x) ^ 2) =
        ∑ x : V,
          ((Fintype.card V : ℝ) ^ 2 * (restrictedDegree R B x : ℝ) ^ 2 -
            2 * (Fintype.card V : ℝ) * (d * B.card : ℕ) *
              restrictedDegree R B x +
            ((d * B.card : ℕ) : ℝ) ^ 2) := by
      apply Finset.sum_congr rfl
      intro x hx
      simp only [scaledCenteredDegree]
      push_cast
      ring
    _ = (Fintype.card V : ℝ) ^ 2 *
          (∑ x : V, (restrictedDegree R B x : ℝ) ^ 2) -
        2 * (Fintype.card V : ℝ) * (d * B.card : ℕ) *
          (∑ x : V, (restrictedDegree R B x : ℝ)) +
        (Fintype.card V : ℝ) * ((d * B.card : ℕ) : ℝ) ^ 2 := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = (Fintype.card V : ℝ) ^ 2 *
          (d * B.card + a * B.card * (B.card - 1) : ℕ) -
        (Fintype.card V : ℝ) * (d * B.card : ℕ) ^ 2 := by
      rw [hfirst, hsecond]
      push_cast
      ring

/-- Explicit squared expander-mixing inequality obtained by combining the
Cauchy bound with the exact second moment. -/
theorem orderedEdges_deviation_sq_le
    (R : V → V → Prop) [DecidableRel R] (d a : ℕ)
    (hsymm : ∀ ⦃x y⦄, R x y → R y x)
    (hdegree : ∀ x, (Finset.univ.filter (R x)).card = d)
    (hcommon : ∀ x y, x ≠ y →
      (Finset.univ.filter fun z ↦ R x z ∧ R y z).card = a)
    (A B : Finset V) :
    ((Fintype.card V : ℝ) * orderedEdges R A B -
        (d : ℝ) * A.card * B.card) ^ 2 ≤
      (A.card : ℝ) *
        ((Fintype.card V : ℝ) ^ 2 *
            (d * B.card + a * B.card * (B.card - 1) : ℕ) -
          (Fintype.card V : ℝ) * (d * B.card : ℕ) ^ 2) := by
  rw [← sum_scaledCenteredDegree_sq R d a hsymm hdegree hcommon B]
  exact orderedEdges_deviation_sq_le_card_mul_sum R d A B

/-- The degree and codegree parameters of a nonempty symmetric design satisfy
the usual relation `d² = d + a (N - 1)`. -/
lemma parameter_identity [Nonempty V]
    (R : V → V → Prop) [DecidableRel R] (d a : ℕ)
    (hsymm : ∀ ⦃x y⦄, R x y → R y x)
    (hdegree : ∀ x, (Finset.univ.filter (R x)).card = d)
    (hcommon : ∀ x y, x ≠ y →
      (Finset.univ.filter fun z ↦ R x z ∧ R y z).card = a) :
    d ^ 2 = d + a * (Fintype.card V - 1) := by
  have hm := sum_restrictedDegree_sq R d a hsymm hdegree hcommon
    (Finset.univ : Finset V)
  have hdres : ∀ x, restrictedDegree R (Finset.univ : Finset V) x = d := by
    intro x
    exact hdegree x
  simp_rw [hdres] at hm
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hm
  have hmul : Fintype.card V * d ^ 2 =
      Fintype.card V * (d + a * (Fintype.card V - 1)) := by
    nlinarith
  exact Nat.eq_of_mul_eq_mul_left Fintype.card_pos hmul

/-- With `N = |V|`, the exact centered second moment is
`N (d-a) |B| (N-|B|)`. -/
lemma sum_scaledCenteredDegree_sq_design [Nonempty V]
    (R : V → V → Prop) [DecidableRel R] (d a : ℕ)
    (hsymm : ∀ ⦃x y⦄, R x y → R y x)
    (hdegree : ∀ x, (Finset.univ.filter (R x)).card = d)
    (hcommon : ∀ x y, x ≠ y →
      (Finset.univ.filter fun z ↦ R x z ∧ R y z).card = a)
    (B : Finset V) :
    ∑ x : V, (scaledCenteredDegree R d B x) ^ 2 =
      (Fintype.card V : ℝ) * ((d : ℝ) - a) * B.card *
        ((Fintype.card V : ℝ) - B.card) := by
  rw [sum_scaledCenteredDegree_sq R d a hsymm hdegree hcommon B]
  have hp := parameter_identity R d a hsymm hdegree hcommon
  have hN : 1 ≤ Fintype.card V := Fintype.card_pos
  by_cases hB : B = ∅
  · simp [hB]
  · have hb : 1 ≤ B.card := (Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hB))
    have hpR : ((d ^ 2 : ℕ) : ℝ) =
        ((d + a * (Fintype.card V - 1) : ℕ) : ℝ) := congrArg _ hp
    push_cast [Nat.cast_sub hN, Nat.cast_sub hb] at hpR ⊢
    linear_combination -(Fintype.card V : ℝ) * (B.card : ℝ) ^ 2 * hpR

/-- Cleared-denominator expander mixing.  This form is convenient for purely
algebraic estimates: no division and no square root occur. -/
theorem scaled_orderedEdges_deviation_sq_le [Nonempty V]
    (R : V → V → Prop) [DecidableRel R] (d a : ℕ)
    (hsymm : ∀ ⦃x y⦄, R x y → R y x)
    (hdegree : ∀ x, (Finset.univ.filter (R x)).card = d)
    (hcommon : ∀ x y, x ≠ y →
      (Finset.univ.filter fun z ↦ R x z ∧ R y z).card = a)
    (ha : a ≤ d) (A B : Finset V) :
    ((Fintype.card V : ℝ) * orderedEdges R A B -
        (d : ℝ) * A.card * B.card) ^ 2 ≤
      (Fintype.card V : ℝ) ^ 2 * ((d : ℝ) - a) * A.card * B.card := by
  have hbase := orderedEdges_deviation_sq_le_card_mul_sum R d A B
  rw [sum_scaledCenteredDegree_sq_design R d a hsymm hdegree hcommon B] at hbase
  have hgap : (Fintype.card V : ℝ) - B.card ≤ Fintype.card V := by
    exact sub_le_self _ (Nat.cast_nonneg B.card)
  have haR : (a : ℝ) ≤ d := by exact_mod_cast ha
  have hcoef : 0 ≤
      (A.card : ℝ) * (Fintype.card V : ℝ) * ((d : ℝ) - a) * B.card := by
    positivity
  calc
    ((Fintype.card V : ℝ) * orderedEdges R A B -
        (d : ℝ) * A.card * B.card) ^ 2 ≤
        (A.card : ℝ) * ((Fintype.card V : ℝ) * ((d : ℝ) - a) *
          B.card * ((Fintype.card V : ℝ) - B.card)) := hbase
    _ ≤ (Fintype.card V : ℝ) ^ 2 * ((d : ℝ) - a) * A.card * B.card := by
      have := mul_le_mul_of_nonneg_left hgap hcoef
      nlinarith

/-- The usual normalized squared expander-mixing inequality. -/
theorem orderedEdges_normalized_deviation_sq_le [Nonempty V]
    (R : V → V → Prop) [DecidableRel R] (d a : ℕ)
    (hsymm : ∀ ⦃x y⦄, R x y → R y x)
    (hdegree : ∀ x, (Finset.univ.filter (R x)).card = d)
    (hcommon : ∀ x y, x ≠ y →
      (Finset.univ.filter fun z ↦ R x z ∧ R y z).card = a)
    (ha : a ≤ d) (A B : Finset V) :
    ((orderedEdges R A B : ℝ) -
        (d : ℝ) / Fintype.card V * A.card * B.card) ^ 2 ≤
      ((d : ℝ) - a) * A.card * B.card := by
  have hclear := scaled_orderedEdges_deviation_sq_le
    R d a hsymm hdegree hcommon ha A B
  have hN : (0 : ℝ) < Fintype.card V := by
    exact_mod_cast Fintype.card_pos
  let z : ℝ := (orderedEdges R A B : ℝ) -
    (d : ℝ) / Fintype.card V * A.card * B.card
  let C : ℝ := ((d : ℝ) - a) * A.card * B.card
  have hscale :
      (Fintype.card V : ℝ) * orderedEdges R A B -
          (d : ℝ) * A.card * B.card =
        (Fintype.card V : ℝ) * z := by
    dsimp [z]
    field_simp
  rw [hscale] at hclear
  have hscaled : (Fintype.card V : ℝ) ^ 2 * z ^ 2 ≤
      (Fintype.card V : ℝ) ^ 2 * C := by
    dsimp [C]
    convert hclear using 1 <;> ring
  have hz := le_of_mul_le_mul_left hscaled (sq_pos_of_pos hN)
  simpa [z, C] using hz

/-- Absolute-value form of expander mixing.  For all finite `A,B`,
`|e(A,B) - d|A||B|/N| ≤ √((d-a)|A||B|)`. -/
theorem abs_orderedEdges_sub_expected_le [Nonempty V]
    (R : V → V → Prop) [DecidableRel R] (d a : ℕ)
    (hsymm : ∀ ⦃x y⦄, R x y → R y x)
    (hdegree : ∀ x, (Finset.univ.filter (R x)).card = d)
    (hcommon : ∀ x y, x ≠ y →
      (Finset.univ.filter fun z ↦ R x z ∧ R y z).card = a)
    (ha : a ≤ d) (A B : Finset V) :
    |(orderedEdges R A B : ℝ) -
        (d : ℝ) / Fintype.card V * A.card * B.card| ≤
      Real.sqrt (((d : ℝ) - a) * A.card * B.card) := by
  apply Real.abs_le_sqrt
  exact orderedEdges_normalized_deviation_sq_le
    R d a hsymm hdegree hcommon ha A B

/-- Summing a pointwise upper bound on restricted degrees. -/
lemma mul_orderedEdges_le_card_mul_of_pointwise
    (R : V → V → Prop) [DecidableRel R] (c : ℕ) (A B : Finset V)
    (h : ∀ x ∈ A, c * restrictedDegree R B x ≤ B.card) :
    c * orderedEdges R A B ≤ A.card * B.card := by
  classical
  rw [orderedEdges, Finset.mul_sum]
  calc
    (∑ x ∈ A, c * restrictedDegree R B x) ≤
        ∑ _x ∈ A, B.card := by
      exact Finset.sum_le_sum fun x hx ↦ h x hx
    _ = A.card * B.card := by simp

/-- A generic poor-set consequence of expander mixing.  The assumptions say
that `d/N ≥ 1/(2Q)`, the actual ordered-edge density is at most `1/(8Q)`,
and `d-a ≤ L`.  The deliberately generous constant `256` is convenient in
applications with coarse projective-space estimates. -/
theorem card_mul_le_of_sparse_orderedEdges [Nonempty V]
    (R : V → V → Prop) [DecidableRel R] (d a : ℕ)
    (hsymm : ∀ ⦃x y⦄, R x y → R y x)
    (hdegree : ∀ x, (Finset.univ.filter (R x)).card = d)
    (hcommon : ∀ x y, x ≠ y →
      (Finset.univ.filter fun z ↦ R x z ∧ R y z).card = a)
    (ha : a ≤ d) (A B : Finset V) (Q L : ℝ)
    (hQ : 0 < Q) (hL : 0 ≤ L)
    (hNd : (Fintype.card V : ℝ) ≤ 2 * Q * d)
    (hvar : (d : ℝ) - a ≤ L)
    (hsparse : 8 * Q * orderedEdges R A B ≤
      (A.card : ℝ) * B.card) :
    (A.card : ℝ) * B.card ≤ 256 * Q ^ 2 * L := by
  have hN : (0 : ℝ) < Fintype.card V := by
    exact_mod_cast Fintype.card_pos
  let X : ℝ := (A.card : ℝ) * B.card
  let E : ℝ := orderedEdges R A B
  let D : ℝ := (d : ℝ) / Fintype.card V * A.card * B.card
  have hX : 0 ≤ X := by positivity
  have hdensity : (1 : ℝ) / (2 * Q) ≤ (d : ℝ) / Fintype.card V := by
    rw [div_le_div_iff₀ (mul_pos (by norm_num) hQ) hN]
    simpa [mul_assoc, mul_comm, mul_left_comm] using hNd
  have hExpected : X / (2 * Q) ≤ D := by
    dsimp [D, X]
    have := mul_le_mul_of_nonneg_right hdensity
      (mul_nonneg (Nat.cast_nonneg A.card) (Nat.cast_nonneg B.card))
    simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using this
  have hEdge : E ≤ X / (8 * Q) := by
    rw [le_div_iff₀ (mul_pos (by norm_num) hQ)]
    dsimp [E, X]
    nlinarith
  have hquarter : X / (4 * Q) ≤ D - E := by
    have htwo : X / (2 * Q) = 2 * (X / (4 * Q)) := by
      field_simp [ne_of_gt hQ]
      ring
    have height : X / (8 * Q) = (X / (4 * Q)) / 2 := by
      field_simp [ne_of_gt hQ]
      ring
    nlinarith [hExpected, hEdge]
  have hquarter_nonneg : 0 ≤ X / (4 * Q) := by positivity
  have hDE_nonneg : 0 ≤ D - E := hquarter_nonneg.trans hquarter
  have hsquare : (X / (4 * Q)) ^ 2 ≤ (E - D) ^ 2 := by
    have hs := (sq_le_sq₀ hquarter_nonneg hDE_nonneg).2 hquarter
    nlinarith
  have hmix := orderedEdges_normalized_deviation_sq_le
    R d a hsymm hdegree hcommon ha A B
  have hmix' : (E - D) ^ 2 ≤ L * X := by
    have hv := mul_le_mul_of_nonneg_right hvar hX
    dsimp [X] at hv
    dsimp [E, D, X]
    have hv' : ((d : ℝ) - a) * A.card * B.card ≤
        L * (A.card * B.card) := by
      simpa [mul_assoc] using hv
    exact hmix.trans hv'
  have hboth : (X / (4 * Q)) ^ 2 ≤ L * X := hsquare.trans hmix'
  by_cases hXzero : X = 0
  · change X ≤ 256 * Q ^ 2 * L
    rw [hXzero]
    positivity
  · have hXpos : 0 < X := lt_of_le_of_ne hX (Ne.symm hXzero)
    have hpoly : X * X ≤ X * (16 * Q ^ 2 * L) := by
      have hscale_nonneg : 0 ≤ (4 * Q) ^ 2 := sq_nonneg _
      have hs := mul_le_mul_of_nonneg_left hboth hscale_nonneg
      calc
        X * X = (4 * Q) ^ 2 * (X / (4 * Q)) ^ 2 := by
          field_simp [ne_of_gt hQ]
        _ ≤ (4 * Q) ^ 2 * (L * X) := hs
        _ = X * (16 * Q ^ 2 * L) := by ring
    have hsmall : X ≤ 16 * Q ^ 2 * L :=
      le_of_mul_le_mul_left hpoly hXpos
    calc
      X ≤ 16 * Q ^ 2 * L := hsmall
      _ ≤ 256 * Q ^ 2 * L := by
        have : 0 ≤ Q ^ 2 * L := mul_nonneg (sq_nonneg Q) hL
        nlinarith

end

end Erdos920.Mixing
