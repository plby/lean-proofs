import ErdosProblems.Erdos1148.FiniteEntropyCollision
import Mathlib.Algebra.BigOperators.Field

/-! # Collision bounds for a finite family with arbitrary positive total mass -/

namespace Erdos1148.DukeArithmetic

lemma finiteEntropy_normalize {ι : Type*} [Fintype ι] (p : ι → ℝ) {m : ℝ}
    (hm : m ≠ 0) (hsum : ∑ i, p i = m) :
    finiteEntropy p = m * finiteEntropy (fun i => p i / m) - m * Real.log m := by
  have hqsum : ∑ i, p i / m = 1 := by rw [← Finset.sum_div, hsum, div_self hm]
  have hterm (i : ι) : Real.negMulLog (p i) =
      m * Real.negMulLog (p i / m) + (p i / m) * Real.negMulLog m := by
    simpa only [div_mul_cancel₀ _ hm] using Real.negMulLog_mul (p i / m) m
  calc
    finiteEntropy p = ∑ i, (m * Real.negMulLog (p i / m) +
        (p i / m) * Real.negMulLog m) := Finset.sum_congr rfl (fun i _ => hterm i)
    _ = m * finiteEntropy (fun i => p i / m) + Real.negMulLog m := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, hqsum, one_mul]
      rfl
    _ = _ := by rw [Real.negMulLog]; ring

theorem neg_mul_log_collision_div_mass_le_finiteEntropy {ι : Type*} [Fintype ι]
    {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i) {m : ℝ} (hm : 0 < m) (hsum : ∑ i, p i = m) :
    -m * Real.log ((∑ i, p i ^ 2) / m) ≤ finiteEntropy p := by
  have hB : 0 < ∑ i, p i ^ 2 := finite_collision_pos_of_sum_pos (by rwa [hsum])
  have hqsum : ∑ i, p i / m = 1 := by rw [← Finset.sum_div, hsum, div_self hm.ne']
  have h := neg_log_collision_le_finiteEntropy (fun i => div_nonneg (hp i) hm.le) hqsum
  have hqcol : (∑ i, (p i / m) ^ 2) = (∑ i, p i ^ 2) / m ^ 2 := by
    simp only [div_pow, Finset.sum_div]
  rw [hqcol] at h
  have hscaled := sub_le_sub_right (mul_le_mul_of_nonneg_left h hm.le) (m * Real.log m)
  calc
    _ = m * -Real.log ((∑ i, p i ^ 2) / m ^ 2) - m * Real.log m := by
      rw [Real.log_div hB.ne' hm.ne', Real.log_div hB.ne' (pow_ne_zero 2 hm.ne'), Real.log_pow]
      ring
    _ ≤ _ := hscaled
    _ = _ := (finiteEntropy_normalize p hm.ne' hsum).symm

end Erdos1148.DukeArithmetic
