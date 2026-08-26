/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierLocalFactor

/-!
# The doubled prime-local polynomial

The switch records whether the companion slope is invertible.  The edge
set records first/companion root collisions.  Both types of exceptional
prime are retained in the polynomial and its zero-exponent value.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

def doubledFourierExceptionalCount {ι : Type*}
    (s : Finset ι) (edges : Finset (ι × ι)) (companion : Bool) : ℕ :=
  (if companion then 0 else s.card) + edges.card

def doubledFourierExceptionalTerm {ι : Type*}
    (s : Finset ι) (edges : Finset (ι × ι)) (companion : Bool)
    (A B : ι → ℂ) : ℂ :=
  (if companion then 0 else -(∑ i ∈ s, B i)) +
    ∑ ij ∈ edges, A ij.1 * B ij.2

def doubledFourierLocalPolynomial {ι : Type*}
    (s : Finset ι) (edges : Finset (ι × ι)) (companion : Bool)
    (p : ℝ) (A B : ι → ℂ) : ℂ :=
  1 + ((∑ i ∈ s, A i) + (if companion then ∑ i ∈ s, B i else 0) +
    ∑ ij ∈ edges, A ij.1 * B ij.2) / p

theorem doubledFourierLocalPolynomial_eq_generic_add_exceptional
    {ι : Type*} (s : Finset ι) (edges : Finset (ι × ι)) (companion : Bool)
    (p : ℝ) (A B : ι → ℂ) :
    doubledFourierLocalPolynomial s edges companion p A B =
      1 + ((∑ i ∈ s, A i) + ∑ i ∈ s, B i) / p +
        doubledFourierExceptionalTerm s edges companion A B / p := by
  cases companion <;>
    simp only [doubledFourierLocalPolynomial, doubledFourierExceptionalTerm,
      Bool.false_eq_true, ↓reduceIte] <;> ring

theorem doubledFourierLocalPolynomial_at_zero_exponents
    {ι : Type*} (s : Finset ι) (edges : Finset (ι × ι)) (companion : Bool)
    (p : ℝ) :
    doubledFourierLocalPolynomial s edges companion p (fun _ ↦ -1) (fun _ ↦ -1) =
      1 - (2 * (s.card : ℂ) - doubledFourierExceptionalCount s edges companion) / p := by
  cases companion <;>
    simp [doubledFourierLocalPolynomial, doubledFourierExceptionalCount] <;> ring

theorem doubledFourierExceptionalTerm_sub_count
    {ι : Type*} (s : Finset ι) (edges : Finset (ι × ι)) (companion : Bool)
    (A B : ι → ℂ) :
    doubledFourierExceptionalTerm s edges companion A B -
        doubledFourierExceptionalCount s edges companion =
      (if companion then 0 else -(∑ i ∈ s, (B i + 1))) +
        ∑ ij ∈ edges, (A ij.1 * B ij.2 - 1) := by
  cases companion
  · simp [doubledFourierExceptionalTerm, doubledFourierExceptionalCount,
      Finset.sum_add_distrib, Finset.sum_sub_distrib]
    ring
  · simp [doubledFourierExceptionalTerm, doubledFourierExceptionalCount,
      Finset.sum_sub_distrib]

theorem norm_mul_sub_one_le_pair_errors (A B : ℂ) :
    ‖A * B - 1‖ ≤ ‖A‖ * ‖B + 1‖ + ‖A + 1‖ := by
  have heq : A * B - 1 = A * (B + 1) - (A + 1) := by ring
  rw [heq]
  simpa only [norm_mul] using norm_sub_le (A * (B + 1)) (A + 1)

/-- Deviation of the exceptional term from its literal integer value.
At a generic prime the switch is true and the edge set is empty, so the
right-hand side is zero, not merely small. -/
theorem norm_doubledFourierExceptionalTerm_sub_count_le
    {ι : Type*} (s : Finset ι) (edges : Finset (ι × ι)) (companion : Bool)
    (A B : ι → ℂ) {δ : ℝ}
    (hA : ∀ i ∈ s, ‖A i‖ ≤ 3)
    (hAe : ∀ i ∈ s, ‖A i + 1‖ ≤ δ)
    (hBe : ∀ i ∈ s, ‖B i + 1‖ ≤ δ)
    (hedges : ∀ ij ∈ edges, ij.1 ∈ s ∧ ij.2 ∈ s) :
    ‖doubledFourierExceptionalTerm s edges companion A B -
        doubledFourierExceptionalCount s edges companion‖ ≤
      ((if companion then 0 else (s.card : ℝ)) + 4 * edges.card) * δ := by
  have hsum : ‖∑ i ∈ s, (B i + 1)‖ ≤ (s.card : ℝ) * δ := by
    calc
      _ ≤ ∑ i ∈ s, ‖B i + 1‖ := norm_sum_le _ _
      _ ≤ ∑ _i ∈ s, δ := Finset.sum_le_sum hBe
      _ = _ := by simp
  have hedgeSum : ‖∑ ij ∈ edges, (A ij.1 * B ij.2 - 1)‖ ≤
      4 * (edges.card : ℝ) * δ := by
    calc
      _ ≤ ∑ ij ∈ edges, ‖A ij.1 * B ij.2 - 1‖ := norm_sum_le _ _
      _ ≤ ∑ _ij ∈ edges, 4 * δ := by
        apply Finset.sum_le_sum
        intro ij hij
        obtain ⟨hi, hj⟩ := hedges ij hij
        calc
          _ ≤ ‖A ij.1‖ * ‖B ij.2 + 1‖ + ‖A ij.1 + 1‖ :=
            norm_mul_sub_one_le_pair_errors _ _
          _ ≤ 3 * δ + δ := by
            exact add_le_add
              (mul_le_mul (hA _ hi) (hBe _ hj) (norm_nonneg _) (by norm_num))
              (hAe _ hi)
          _ = _ := by ring
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring
  rw [doubledFourierExceptionalTerm_sub_count]
  cases companion
  · simp only [Bool.false_eq_true, ↓reduceIte]
    calc
      _ ≤ ‖∑ i ∈ s, (B i + 1)‖ +
          ‖∑ ij ∈ edges, (A ij.1 * B ij.2 - 1)‖ := by
        simpa only [norm_neg] using norm_add_le
          (-(∑ i ∈ s, (B i + 1))) (∑ ij ∈ edges, (A ij.1 * B ij.2 - 1))
      _ ≤ (s.card : ℝ) * δ + 4 * (edges.card : ℝ) * δ :=
        add_le_add hsum hedgeSum
      _ = _ := by ring
  · simpa using hedgeSum

end

end Erdos4b
