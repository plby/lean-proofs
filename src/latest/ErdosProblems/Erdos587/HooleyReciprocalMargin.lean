import ErdosProblems.Erdos587.HooleyPowerMargin

/-! # The reciprocal short-range cost is absorbed by power separation -/

namespace Erdos587

theorem exists_delta_reciprocal_margin_bound (r : ℕ) (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ X D : ℕ, 1 ≤ X → 2 ^ D ≤ X → ∀ K R : ℝ, 0 ≤ K →
      K * (X : ℝ) ^ (3 / (r : ℝ)) ≤ R →
      K ^ 2 * (deltaProgressionCutoff r X + 2) * (D + 3) * (X : ℝ) ^ (r : ℝ)⁻¹ ≤
        C * R * K := by
  let A := (r : ℝ) / Real.log 2 + 3
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hA : 0 < A := by dsimp only [A]; positivity
  refine ⟨20 * A, by positivity, ?_⟩
  intro X D hX hD K R hK hsep
  let T := (X : ℝ) ^ (r : ℝ)⁻¹
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hT1 : 1 ≤ T := Real.one_le_rpow (by exact_mod_cast hX) (by positivity)
  have hT : 0 ≤ T := le_trans zero_le_one hT1
  have hY := deltaProgressionCutoff_le hr hX
  have hY' : (deltaProgressionCutoff r X : ℝ) + 2 ≤ 20 * T := by
    change (deltaProgressionCutoff r X : ℝ) ≤ 18 * T at hY
    linarith
  have hD' : (D : ℝ) + 3 ≤ A * T := delta_dyadic_scale_rpow_bound hr hX hD
  have hpower : T ^ 3 = (X : ℝ) ^ (3 / (r : ℝ)) := by
    dsimp only [T]
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg X)]
    congr 1
    norm_num
    ring
  calc
    _ ≤ K ^ 2 * (20 * T) * (A * T) * T := by
      apply mul_le_mul_of_nonneg_right _ hT
      exact mul_le_mul (mul_le_mul_of_nonneg_left hY' (sq_nonneg K)) hD'
        (by positivity) (by positivity)
    _ = (20 * A * K) * (K * T ^ 3) := by ring
    _ ≤ (20 * A * K) * R := by
      rw [hpower]
      exact mul_le_mul_of_nonneg_left hsep (by positivity)
    _ = _ := by ring

end Erdos587
