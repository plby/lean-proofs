import ErdosProblems.Erdos587.QuarticBudgets

/-! One cubic surplus supplies all three terminal power budgets. -/

namespace Erdos587

theorem terminal_budgets_of_cubic_surplus {H N S F D E Λ : ℝ} (B : ℕ)
    (hH : 0 ≤ H) (hN : 0 ≤ N) (hS : 0 ≤ S) (hF : 0 ≤ F)
    (hD : 1 ≤ D) (hΛ : 1 ≤ Λ)
    (hEside : F ^ 4 * S ≤ E) (hEone : 16 * D ^ 2 * S ≤ E)
    (hlarge : E * N * Λ ^ (4 * B) ≤ H ^ 3) :
    F ^ 4 * (S * H * N) * Λ ^ (4 * B) ≤ H ^ 4 ∧
    D ^ 4 * (S * H * N) ^ 3 * Λ ^ (4 * B) ≤ H ^ 12 ∧
    16 * D ^ 2 * (S * H * N) ≤ H ^ 4 := by
  have hD0 : 0 ≤ D := by linarith
  have hΛ0 : 0 ≤ Λ := by linarith
  have hlogpow : 1 ≤ Λ ^ (4 * B) := one_le_pow₀ hΛ
  have hDE : D ^ 2 * S ≤ E := by nlinarith only [hEone, sq_nonneg D, hS]
  have hE : 0 ≤ E := le_trans (by positivity) hDE
  have hcoeff : D ^ 4 * S ^ 3 ≤ E ^ 3 := by
    calc
      D ^ 4 * S ^ 3 ≤ D ^ 6 * S ^ 3 :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hD (by omega)) (by positivity)
      _ = (D ^ 2 * S) ^ 3 := by ring
      _ ≤ E ^ 3 := pow_le_pow_left₀ (by positivity) hDE 3
  have hlogcube : Λ ^ (4 * B) ≤ (Λ ^ (4 * B)) ^ 3 := by
    simpa only [pow_one] using pow_le_pow_right₀ hlogpow (show 1 ≤ 3 by omega)
  refine ⟨?_, ?_, ?_⟩
  · calc
      F ^ 4 * (S * H * N) * Λ ^ (4 * B) = H * ((F ^ 4 * S) * N * Λ ^ (4 * B)) := by ring
      _ ≤ H * (E * N * Λ ^ (4 * B)) := by gcongr
      _ ≤ H * H ^ 3 := mul_le_mul_of_nonneg_left hlarge hH
      _ = H ^ 4 := by ring
  · calc
      D ^ 4 * (S * H * N) ^ 3 * Λ ^ (4 * B) =
          H ^ 3 * (D ^ 4 * S ^ 3) * N ^ 3 * Λ ^ (4 * B) := by ring
      _ ≤ H ^ 3 * E ^ 3 * N ^ 3 * (Λ ^ (4 * B)) ^ 3 := by gcongr
      _ = H ^ 3 * (E * N * Λ ^ (4 * B)) ^ 3 := by ring
      _ ≤ H ^ 3 * (H ^ 3) ^ 3 := by gcongr
      _ = H ^ 12 := by ring
  · calc
      16 * D ^ 2 * (S * H * N) = H * ((16 * D ^ 2 * S) * N) := by ring
      _ ≤ H * (E * N) := by gcongr
      _ ≤ H * (E * N * Λ ^ (4 * B)) := mul_le_mul_of_nonneg_left
        (le_mul_of_one_le_right (mul_nonneg hE hN) hlogpow) hH
      _ ≤ H * H ^ 3 := mul_le_mul_of_nonneg_left hlarge hH
      _ = H ^ 4 := by ring

end Erdos587
