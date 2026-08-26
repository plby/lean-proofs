/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierRelativeComparison
import ErdosProblems.Erdos4b.GeneralFourierPrimeMass
import BoundedGaps.Arithmetic.SquarefreeReciprocalCoefficient

/-!
# Uniform finite products of the relative Fourier errors

The generic reciprocal-square tail is bounded independently of the prime
cutoff. The exceptional first-order perturbation is charged to the
logarithmic prime-divisor mass of an actual positive integer.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

theorem fourierPairComparisonConstant_nonneg (N : ℕ) :
    0 ≤ fourierPairComparisonConstant N := by
  have h := pairProductErrorConstant_nonneg N
  unfold fourierPairComparisonConstant
  positivity

theorem doubledFourierExceptionalCost_nonneg {ι : Type*} [Fintype ι]
    (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool) (p : ℕ) :
    0 ≤ doubledFourierExceptionalCost edges companion p := by
  unfold doubledFourierExceptionalCost
  split_ifs <;> positivity

theorem doubledFourierExceptionalCost_le_five_card {ι : Type*} [Fintype ι]
    (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool) {p : ℕ}
    (hcard : (edges p).card ≤ Fintype.card ι) :
    doubledFourierExceptionalCost edges companion p ≤ 5 * (Fintype.card ι : ℝ) := by
  have hcardR : ((edges p).card : ℝ) ≤ Fintype.card ι := by exact_mod_cast hcard
  have hk : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  unfold doubledFourierExceptionalCost
  split_ifs <;> linarith

theorem finite_rough_reciprocalSquare_sum_le
    (P : Finset ℕ) {w : ℕ} (hw : 0 < w) (hrough : ∀ p ∈ P, w < p) :
    (∑ p ∈ P, (1 : ℝ) / (p : ℝ) ^ 2) ≤ 2 / (w : ℝ) := by
  let Q := max w (P.sup id) + 1
  have hsub : P ⊆ Finset.Ico w Q := by
    intro p hp
    exact Finset.mem_Ico.mpr ⟨(hrough p hp).le,
      Nat.lt_succ_of_le ((Finset.le_sup (f := id) hp).trans (le_max_right _ _))⟩
  exact (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p hp hpnot ↦ by positivity)).trans
    (BoundedGaps.Maynard.sum_Ico_one_div_nat_sq_le hw
      (by dsimp [Q]; omega))

theorem finite_rough_primeLog_divisor_sum_le
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) {M : ℕ} (hM : 0 < M)
    (w : ℕ) (hrough : ∀ p ∈ P, w < p) :
    (∑ p ∈ P, if p ∣ M then Real.log p / (p : ℝ) else 0) ≤ roughPrimeLogDivisorMass M w := by
  classical
  rw [← Finset.sum_filter]
  unfold roughPrimeLogDivisorMass
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    obtain ⟨hpP, hpM⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr
      ⟨Nat.mem_primeFactors.mpr ⟨hP p hpP, hpM, hM.ne'⟩, hrough p hpP⟩
  · intro p hp hpnot
    positivity

theorem doubledFourierExceptionalCost_perturbation_le
    {ι : Type*} [Fintype ι] (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    {p M : ℕ} {σ : ℝ} (hp : p.Prime) (hσ : 0 ≤ σ)
    (hedgeCard : (edges p).card ≤ Fintype.card ι)
    (hgeneric : ¬p ∣ M → edges p = ∅ ∧ companion p = true) :
    doubledFourierExceptionalCost edges companion p * (2 * σ * Real.log p) / p ≤
      (10 * (Fintype.card ι : ℝ) * σ) *
        (if p ∣ M then Real.log p / (p : ℝ) else 0) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hlog : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  by_cases hpM : p ∣ M
  · rw [if_pos hpM]
    calc
      _ ≤ (5 * (Fintype.card ι : ℝ)) * (2 * σ * Real.log p) / p := by
        apply div_le_div_of_nonneg_right _ hp0.le
        exact mul_le_mul_of_nonneg_right
          (doubledFourierExceptionalCost_le_five_card edges companion hedgeCard) (by positivity)
      _ = _ := by ring
  · obtain ⟨he, hc⟩ := hgeneric hpM
    simp [doubledFourierExceptionalCost, he, hc, hpM]

theorem sum_norm_doubledFourierRelativeFactor_sub_one_le
    {ι : Type*} [Fintype ι] (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (s : (ι ⊕ ι) → Bool → ℂ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {M w : ℕ} {σ : ℝ} (hM : 0 < M) (hw : 0 < w) (hσ : 0 ≤ σ)
    (hrough : ∀ p ∈ P, w < p)
    (hcard : ∀ p ∈ P, 7 * (Fintype.card (ι ⊕ ι) : ℝ) ≤ p)
    (hedgeCard : ∀ p ∈ P, (edges p).card ≤ Fintype.card ι)
    (hgeneric : ∀ p ∈ P, ¬p ∣ M → edges p = ∅ ∧ companion p = true)
    (hRe : ∀ i b, 0 ≤ (s i b).re) (hNorm : ∀ i, ‖s i false‖ ≤ σ) :
    (∑ p ∈ P, ‖doubledFourierRelativeFactor edges companion s p - 1‖) ≤
      2 * (12 : ℝ) ^ Fintype.card (ι ⊕ ι) *
        (fourierPairComparisonConstant (Fintype.card (ι ⊕ ι)) * (2 / (w : ℝ)) +
          (10 * (Fintype.card ι : ℝ) * σ) * roughPrimeLogDivisorMass M w) := by
  let A := 2 * (12 : ℝ) ^ Fintype.card (ι ⊕ ι)
  let C := fourierPairComparisonConstant (Fintype.card (ι ⊕ ι))
  let E := 10 * (Fintype.card ι : ℝ) * σ
  have hA : 0 ≤ A := by positivity
  have hC : 0 ≤ C := fourierPairComparisonConstant_nonneg _
  have hE : 0 ≤ E := by dsimp [E]; positivity
  calc
    _ ≤ ∑ p ∈ P, A * (C / (p : ℝ) ^ 2 +
        E * (if p ∣ M then Real.log p / (p : ℝ) else 0)) := by
      apply Finset.sum_le_sum
      intro p hp
      apply (norm_doubledFourierRelativeFactor_sub_one_le edges companion s
        (by exact_mod_cast (hP p hp).two_le) (hcard p hp) (hedgeCard p hp) hRe hNorm).trans
      apply mul_le_mul_of_nonneg_left _ hA
      exact add_le_add le_rfl (doubledFourierExceptionalCost_perturbation_le edges companion
        (hP p hp) hσ (hedgeCard p hp) (hgeneric p hp))
    _ = A * (C * (∑ p ∈ P, (1 : ℝ) / (p : ℝ) ^ 2) +
        E * (∑ p ∈ P, if p ∣ M then Real.log p / (p : ℝ) else 0)) := by
      simp only [Finset.mul_sum, mul_add, Finset.sum_add_distrib, mul_one_div]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ hA
      exact add_le_add
        (mul_le_mul_of_nonneg_left (finite_rough_reciprocalSquare_sum_le P hw hrough) hC)
        (mul_le_mul_of_nonneg_left (finite_rough_primeLog_divisor_sum_le P hP hM w hrough) hE)

theorem norm_prod_doubledFourierRelativeFactor_sub_one_le
    {ι : Type*} [Fintype ι] (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (s : (ι ⊕ ι) → Bool → ℂ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {M w : ℕ} {σ : ℝ} (hM : 0 < M) (hw : 0 < w) (hσ : 0 ≤ σ)
    (hrough : ∀ p ∈ P, w < p)
    (hcard : ∀ p ∈ P, 7 * (Fintype.card (ι ⊕ ι) : ℝ) ≤ p)
    (hedgeCard : ∀ p ∈ P, (edges p).card ≤ Fintype.card ι)
    (hgeneric : ∀ p ∈ P, ¬p ∣ M → edges p = ∅ ∧ companion p = true)
    (hRe : ∀ i b, 0 ≤ (s i b).re) (hNorm : ∀ i, ‖s i false‖ ≤ σ) :
    ‖(∏ p ∈ P, doubledFourierRelativeFactor edges companion s p) - 1‖ ≤
      Real.exp (2 * (12 : ℝ) ^ Fintype.card (ι ⊕ ι) *
        (fourierPairComparisonConstant (Fintype.card (ι ⊕ ι)) * (2 / (w : ℝ)) +
          (10 * (Fintype.card ι : ℝ) * σ) * roughPrimeLogDivisorMass M w)) - 1 := by
  have hsum := sum_norm_doubledFourierRelativeFactor_sub_one_le edges companion s P hP
    hM hw hσ hrough hcard hedgeCard hgeneric hRe hNorm
  have hprod := norm_prod_one_add_error_le P
    (fun p ↦ doubledFourierRelativeFactor edges companion s p - 1)
  simp only [add_sub_cancel] at hprod
  exact hprod.trans (sub_le_sub_right (Real.exp_le_exp.mpr hsum) 1)

end

end Erdos4b
