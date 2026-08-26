/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierFiniteNormalization

/-!
# Endpoint errors controlled by the actual coefficient mass

The endpoint estimate uses the first absolute moment of the coefficient,
so an artificially large finite prime cutoff does not enlarge the bound
through zero coefficients outside the true profile support.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

def doubledSelbergCoefficientMass (H : Finset ℕ) (D E : Finset (H → ℕ))
    (lambda : (H → ℕ) → (H → ℕ) → ℝ) : ℝ :=
  ∑ d ∈ D, ∑ e ∈ E, |lambda d e|

theorem sum_fourfold_product_eq_square {ι κ : Type*}
    (D : Finset ι) (E : Finset κ) (f : ι → κ → ℝ) (R : ℝ) :
    (∑ d ∈ D, ∑ e ∈ E, ∑ d' ∈ D, ∑ e' ∈ E, f d e * f d' e' * R) =
      (∑ d ∈ D, ∑ e ∈ E, f d e) ^ 2 * R := by
  have hinner (d : ι) (e : κ) :
      (∑ d' ∈ D, ∑ e' ∈ E, f d e * f d' e' * R) =
        f d e * (∑ d' ∈ D, ∑ e' ∈ E, f d' e') * R := by
    simp_rw [← Finset.sum_mul, ← Finset.mul_sum]
  simp_rw [hinner, ← Finset.sum_mul]
  ring

theorem doubledSelbergGeneralNormalizationError_abs_le_mass
    (H : Finset ℕ) (D E : Finset (H → ℕ))
    (lambda : (H → ℕ) → (H → ℕ) → ℝ) (W m q T : ℕ)
    (support : DoubledSelbergGeneralSupport H D E m) (hW : 0 < W) :
    |doubledSelbergGeneralNormalizationError H D E lambda W m q T| ≤
      doubledSelbergCoefficientMass H D E lambda ^ 2 *
        (allowedPreSieveResidues W m).card := by
  let err (d e d' e' : H → ℕ) :=
    ∑ v ∈ allowedPreSieveResidues W m,
      largeGapGeneralCrtClassError H W v m q T d e d' e'
  have herr (d : H → ℕ) (hd : d ∈ D) (e : H → ℕ) (he : e ∈ E)
      (d' : H → ℕ) (hd' : d' ∈ D) (e' : H → ℕ) (he' : e' ∈ E) :
      |err d e d' e'| ≤ (allowedPreSieveResidues W m).card := by
    calc
      _ ≤ ∑ v ∈ allowedPreSieveResidues W m,
          |largeGapGeneralCrtClassError H W v m q T d e d' e'| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _v ∈ allowedPreSieveResidues W m, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro v hv
        exact largeGapGeneralCrtClassError_abs_le_one H W v m q T d e d' e' hW
          (support.first_lcm_pos d hd d' hd') (support.companion_lcm_pos e he e' he')
      _ = _ := by simp
  change |∑ d ∈ D, ∑ e ∈ E, ∑ d' ∈ D, ∑ e' ∈ E,
    lambda d e * lambda d' e' * err d e d' e'| ≤ _
  calc
    _ ≤ ∑ d ∈ D, ∑ e ∈ E, ∑ d' ∈ D, ∑ e' ∈ E,
        |lambda d e * lambda d' e' * err d e d' e'| := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro d hd
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro e he
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro d' hd'
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ D, ∑ e ∈ E, ∑ d' ∈ D, ∑ e' ∈ E,
        |lambda d e| * |lambda d' e'| * (allowedPreSieveResidues W m).card := by
      apply Finset.sum_le_sum
      intro d hd
      apply Finset.sum_le_sum
      intro e he
      apply Finset.sum_le_sum
      intro d' hd'
      apply Finset.sum_le_sum
      intro e' he'
      rw [abs_mul, abs_mul]
      exact mul_le_mul_of_nonneg_left (herr d hd e he d' hd' e' he') (by positivity)
    _ = _ := sum_fourfold_product_eq_square D E (fun d e ↦ |lambda d e|) _

end

end Erdos4b
