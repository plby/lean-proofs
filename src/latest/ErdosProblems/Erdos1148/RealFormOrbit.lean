import ErdosProblems.Erdos1148.RealFlow

/-!
# The real orbit of a positive-discriminant form

An explicit matrix takes a nonzero multiple of `xy` to any real form
with the same discriminant. No orbit-transitivity theorem is assumed.
-/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

lemma exists_transform_splitForm {t : ℝ × ℝ × ℝ} {ρ : ℝ}
    (hρ : ρ ≠ 0) (ht : discr t = ρ ^ 2) :
    ∃ M : Matrix (Fin 2) (Fin 2) ℝ, M.det = 1 ∧ ρ • transform M (splitForm ℝ) = t := by
  rcases t with ⟨a, b, c⟩
  change b ^ 2 - 4 * a * c = ρ ^ 2 at ht
  by_cases ha : a = 0
  · have hb : b = ρ ∨ b = -ρ := sq_eq_sq_iff_eq_or_eq_neg.mp (by simpa [ha] using ht)
    rcases hb with hb | hb
    · refine ⟨!![1, c / ρ; 0, 1], by simp [Matrix.det_fin_two], ?_⟩
      ext <;> dsimp [transform, splitForm] <;> simp [ha, hb] <;> field_simp
    · refine ⟨!![0, -1; 1, -c / ρ], by simp [Matrix.det_fin_two], ?_⟩
      ext <;> dsimp [transform, splitForm] <;> simp [ha, hb] <;> field_simp
  · refine ⟨!![a / ρ, (b - ρ) / (2 * ρ); 1, (b + ρ) / (2 * a)], ?_, ?_⟩
    · rw [Matrix.det_fin_two]
      dsimp
      field_simp
      ring
    · ext <;> dsimp [transform, splitForm]
      all_goals simp only [zero_mul, mul_zero, zero_add, add_zero, one_mul, mul_one]
      all_goals field_simp
      all_goals nlinarith

theorem exists_formAction_splitForm {t : ℝ × ℝ × ℝ} {ρ : ℝ}
    (hρ : ρ ≠ 0) (ht : discr t = ρ ^ 2) :
    ∃ g : SL(2, ℝ), ρ • formAction g (splitForm ℝ) = t := by
  obtain ⟨M, hM, htM⟩ := exists_transform_splitForm hρ ht
  let g : SL(2, ℝ) := ⟨M, hM⟩
  refine ⟨g⁻¹, ?_⟩
  change ρ • transform ((g⁻¹)⁻¹ : SL(2, ℝ)) (splitForm ℝ) = t
  rw [inv_inv]
  exact htM

theorem exists_formAction_sqrt_discr {d : ℝ} (hd : 0 < d)
    {t : ℝ × ℝ × ℝ} (ht : discr t = d) :
    ∃ g : SL(2, ℝ), Real.sqrt d • formAction g (splitForm ℝ) = t := by
  apply exists_formAction_splitForm (Real.sqrt_pos.mpr hd).ne'
  rw [Real.sq_sqrt hd.le]
  exact ht

end Erdos1148.DukeArithmetic
