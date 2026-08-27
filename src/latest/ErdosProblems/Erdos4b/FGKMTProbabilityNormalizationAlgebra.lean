/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTTotalRelativeAlgebra

/-! # Explicit errors when normalizing a finite family of weights -/

namespace Erdos4b.FGKMT

open scoped BigOperators

theorem mass_pos_of_relative_error {M T d : ℝ}
    (hT : 0 < T) (hd : d ≤ 1 / 2) (hM : |M - T| ≤ d * T) :
    T / 2 ≤ M ∧ 0 < M := by
  have h := (abs_le.mp hM).1
  have hhalf := mul_le_mul_of_nonneg_right hd hT.le
  constructor <;> linarith

theorem normalized_atom_error {a M T d : ℝ}
    (ha : 0 ≤ a) (hT : 0 < T) (hd0 : 0 ≤ d) (hd : d ≤ 1 / 2)
    (hM : |M - T| ≤ d * T) :
    |a / M - a / T| ≤ 2 * d * (a / T) := by
  obtain ⟨hhalf, hMpos⟩ := mass_pos_of_relative_error hT hd hM
  have hsmall : |T - M| / M ≤ 2 * d := by
    apply (div_le_iff₀ hMpos).mpr
    rw [abs_sub_comm]
    exact hM.trans (by nlinarith [mul_le_mul_of_nonneg_left hhalf hd0])
  have hid : a / M - a / T = (a / T) * ((T - M) / M) := by
    field_simp
  rw [hid, abs_mul, abs_of_nonneg (div_nonneg ha hT.le), abs_div, abs_of_pos hMpos]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hsmall (div_nonneg ha hT.le)

theorem normalized_finite_sum_error {α : Type*} (P : Finset α)
    (a M : α → ℝ) {T U d : ℝ}
    (ha : ∀ p ∈ P, 0 ≤ a p) (hT : 0 < T) (hU : 0 < U)
    (hd0 : 0 ≤ d) (hd : d ≤ 1 / 2)
    (hM : ∀ p ∈ P, |M p - T| ≤ d * T)
    (hA : |(∑ p ∈ P, a p) - U| ≤ d * U) :
    |(∑ p ∈ P, a p / M p) - U / T| ≤ 4 * d * (U / T) := by
  have hdiff : |(∑ p ∈ P, a p / M p) - (∑ p ∈ P, a p) / T| ≤
      2 * d * ((∑ p ∈ P, a p) / T) := by
    calc
      _ = |∑ p ∈ P, (a p / M p - a p / T)| := by rw [Finset.sum_sub_distrib, Finset.sum_div]
      _ ≤ ∑ p ∈ P, |a p / M p - a p / T| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ p ∈ P, 2 * d * (a p / T) :=
        Finset.sum_le_sum fun p hp => normalized_atom_error (ha p hp) hT hd0 hd (hM p hp)
      _ = _ := by rw [← Finset.mul_sum, Finset.sum_div]
  have hmean : |(∑ p ∈ P, a p) / T - U / T| ≤ d * (U / T) := by
    rw [← sub_div, abs_div, abs_of_pos hT]
    simpa only [mul_div_assoc] using (div_le_div_of_nonneg_right hA hT.le)
  have hsum : (∑ p ∈ P, a p) ≤ (1 + d) * U := by
    have hh := (abs_le.mp hA).2
    linarith
  have hsumdiv := div_le_div_of_nonneg_right hsum hT.le
  have hsumscaled := mul_le_mul_of_nonneg_left hsumdiv (by positivity : 0 ≤ 2 * d)
  simp only [mul_div_assoc] at hsumscaled
  have hdhalf := mul_le_mul_of_nonneg_left hd hd0
  have hUdiv : 0 ≤ U / T := div_nonneg hU.le hT.le
  calc
    _ ≤ |(∑ p ∈ P, a p / M p) - (∑ p ∈ P, a p) / T| +
        |(∑ p ∈ P, a p) / T - U / T| := abs_sub_le _ _ _
    _ ≤ 2 * d * ((∑ p ∈ P, a p) / T) + d * (U / T) := add_le_add hdiff hmean
    _ ≤ _ := by
      have hlast := mul_le_mul_of_nonneg_right hdhalf hUdiv
      nlinarith

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.normalized_atom_error
#print axioms Erdos4b.FGKMT.normalized_finite_sum_error
