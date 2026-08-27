import ErdosProblems.Erdos587.HooleyFractionalCoefficients

/-! # Coordinatewise rounding of a zonotope point to an actual subset sum -/

open scoped BigOperators

namespace Erdos587.CFP

theorem delta_exists_subset_sum_coordinate_rounding {ι : Type*} [Fintype ι] {d : ℕ}
    (v : ι → Fin d → ℝ) (L : Fin d → ℝ) (hL : ∀ j, 0 ≤ L j)
    (hv : ∀ i j, |v i j| ≤ L j) (α : ι → ℝ)
    (hα : ∀ i, α i ∈ Set.Icc (0 : ℝ) 1) :
    ∃ S : Finset ι, ∀ j,
      |(∑ i, α i * v i j) - ∑ i ∈ S, v i j| ≤ (d : ℝ) * L j := by
  classical
  obtain ⟨β, hβ, hsum, hfrac⟩ := delta_exists_few_fractional_coefficients v α hα
  let S := Finset.univ.filter (fun i => β i = 1)
  let F := Finset.univ.filter (fun i => 0 < β i ∧ β i < 1)
  refine ⟨S, ?_⟩
  intro j
  have hcoord : (∑ i, β i * v i j) = ∑ i, α i * v i j := by
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using congrFun hsum j
  have hdecomp : (∑ i, β i * v i j) - ∑ i ∈ S, v i j =
      ∑ i ∈ F, β i * v i j := by
    dsimp only [S, F]
    rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi1 : β i = 1
    · simp [hi1]
    by_cases hi0 : β i = 0
    · simp [hi0]
    have hi : 0 < β i ∧ β i < 1 :=
      ⟨lt_of_le_of_ne (hβ i).1 (Ne.symm hi0), lt_of_le_of_ne (hβ i).2 hi1⟩
    simp only [if_neg hi1, if_pos hi, sub_zero]
  rw [← hcoord, hdecomp]
  calc
    _ ≤ ∑ i ∈ F, |β i * v i j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ F, L j := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul, abs_of_nonneg (hβ i).1]
      exact (mul_le_mul (hβ i).2 (hv i j) (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
    _ = (F.card : ℝ) * L j := by simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (d : ℝ) * L j := mul_le_mul_of_nonneg_right (by exact_mod_cast hfrac) (hL j)

end Erdos587.CFP
