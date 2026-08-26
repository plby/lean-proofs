import ErdosProblems.Erdos421.LogOverlapScale
import ErdosProblems.Erdos421.MeanValueDefectDecay

/-! # Substituting the complete mean-value theorem in the logarithmic moment bound -/

namespace Erdos421

theorem vinogradovCount_weighted_small_defect {k : ℕ} (hk : 2 ≤ k) (r M : ℕ)
    (hr : 2 * (k : ℝ) * Real.log k ≤ r) (hM : 0 < M) :
    (M : ℝ) ^ (k + meanValueTriangle k) * (vinogradovCount ((r + 1) * k) k M : ℝ) ≤
      (2 : ℝ) ^ (32 * (k + 1) ^ 5 * (r + 1) ^ 3) * (M : ℝ) ^ (2 * ((r + 1) * k) + 1) := by
  have hMp : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  have h := vinogradovCount_complete_meanValue_small_defect hk r M hr hM
  calc
    _ ≤ (M : ℝ) ^ (k + meanValueTriangle k) *
        ((2 : ℝ) ^ (32 * (k + 1) ^ 5 * (r + 1) ^ 3) *
          (M : ℝ) ^ (2 * (((r + 1) * k : ℕ) : ℝ) -
            ((k + meanValueTriangle k : ℕ) : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by
      rw [mul_left_comm, ← Real.rpow_natCast (M : ℝ) (k + meanValueTriangle k),
        ← Real.rpow_add hMp]
      have he : ((k + meanValueTriangle k : ℕ) : ℝ) +
          (2 * (((r + 1) * k : ℕ) : ℝ) - ((k + meanValueTriangle k : ℕ) : ℝ) + 1) =
            ((2 * ((r + 1) * k) + 1 : ℕ) : ℝ) := by push_cast; ring
      rw [he, Real.rpow_natCast]

noncomputable def logarithmicMeanValueConstant (k r : ℕ) : ℝ :=
  (Real.pi * k) ^ k * k.factorial * (2 : ℝ) ^ (2 * k + 5) *
    (3 : ℝ) ^ (2 * ((r + 1) * k)) * (2 : ℝ) ^ (32 * (k + 1) ^ 5 * (r + 1) ^ 3)

theorem logarithmicMeanValueConstant_nonneg (k r : ℕ) : 0 ≤ logarithmicMeanValueConstant k r := by
  unfold logarithmicMeanValueConstant
  positivity

theorem logarithmicMomentUpper_le_power {k M N : ℕ} (hk : 2 ≤ k) (hM : 0 < M) (r : ℕ)
    (hr : 2 * (k : ℝ) * Real.log k ≤ r) {A t : ℝ} (hA : 0 < A) (ht : t ≠ 0)
    (hNA : (N : ℝ) ≤ A) (hscale : A ^ (k + 1) ≤ |t| * (2 * (M : ℝ)) ^ (k + 1)) :
    logarithmicMomentUpper k ((r + 1) * k) M N t A ≤
      logarithmicMeanValueConstant k r * (M : ℝ) ^ (2 * ((r + 1) * k) + 3) := by
  let W : ℝ := 1 + 2 * (A + N) ^ (k + 1) / ((k : ℝ) ^ 2 * |t| * (M : ℝ) ^ k)
  have hW : W ≤ (2 : ℝ) ^ (2 * k + 4) * M :=
    logarithmic_overlap_factor_le (by omega) hM hA ht hNA hscale
  have hMplus : ((M + 1 : ℕ) : ℝ) ≤ 2 * (M : ℝ) := by exact_mod_cast (by omega : M + 1 ≤ 2 * M)
  have hJ := vinogradovCount_weighted_small_defect hk r M hr hM
  calc
    _ = ((Real.pi * k) ^ k * k.factorial * (3 : ℝ) ^ (2 * ((r + 1) * k))) *
        W * (M + 1 : ℕ) *
          ((M : ℝ) ^ (k + meanValueTriangle k) * (vinogradovCount ((r + 1) * k) k M : ℝ)) := by
      unfold logarithmicMomentUpper
      dsimp only [W]
      ring
    _ ≤ ((Real.pi * k) ^ k * k.factorial * (3 : ℝ) ^ (2 * ((r + 1) * k))) *
        ((2 : ℝ) ^ (2 * k + 4) * M) * (2 * (M : ℝ)) *
          ((2 : ℝ) ^ (32 * (k + 1) ^ 5 * (r + 1) ^ 3) *
            (M : ℝ) ^ (2 * ((r + 1) * k) + 1)) := by
      apply mul_le_mul _ hJ (by positivity) (by positivity)
      exact mul_le_mul (mul_le_mul_of_nonneg_left hW (by positivity)) hMplus
        (by positivity) (by positivity)
    _ = _ := by
      unfold logarithmicMeanValueConstant
      rw [show 2 * k + 5 = (2 * k + 4) + 1 by omega, pow_succ (2 : ℝ) (2 * k + 4),
        show 2 * ((r + 1) * k) + 3 = (2 * ((r + 1) * k) + 1) + 2 by omega,
        pow_add (M : ℝ) (2 * ((r + 1) * k) + 1) 2, pow_two]
      ring

end Erdos421
