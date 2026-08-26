import ErdosProblems.Erdos856b.Extrema

/-! # The elementary optimization in Theorem 1.1 of the selected writeup -/

namespace Erdos856b

open Real
open scoped BigOperators

/-- The finite-block contribution, written with `exp` to simplify the optimization. -/
noncomputable def blockValue (n r : ℕ) (size : ℝ) : ℝ :=
  (r : ℝ) * exp (log size / r - 1) / n

theorem log_weight_le_root {r z : ℝ} (hr : 0 < r) (hz : 0 < z) (size : ℝ) :
    log size + r * log z ≤ r * exp (log size / r - 1) * z := by
  have h := Real.log_le_sub_one_of_pos (mul_pos hz (exp_pos (log size / r - 1)))
  rw [log_mul hz.ne' (exp_ne_zero _), log_exp] at h
  have hmul := mul_le_mul_of_nonneg_left h hr.le
  have hcancel : r * (log size / r) = log size := by field_simp
  nlinarith

theorem blockValue_eq_rpow {n r : ℕ} {size : ℝ} (hsize : 0 < size) :
    blockValue n r size = (r : ℝ) / (exp 1 * n) * size ^ (1 / (r : ℝ)) := by
  rw [blockValue, rpow_def_of_pos hsize, exp_sub]
  rw [show log size * (1 / (r : ℝ)) = log size / r by ring]
  ring

theorem blockValue_eq_log_weight {n r : ℕ} (hn : 0 < n) (hr : 0 < r) (size : ℝ) :
    blockValue n r size =
      (log size + r * log (exp (1 - log size / r))) /
        (n * exp (1 - log size / r)) := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hr0 : (r : ℝ) ≠ 0 := by positivity
  rw [blockValue, log_exp]
  have hexp : exp (1 - log size / r) = (exp (log size / r - 1))⁻¹ := by
    rw [← exp_neg]
    congr 1
    ring
  rw [hexp]
  field_simp
  ring

theorem log_weight_div_le_blockValue {n r : ℕ} (hn : 0 < n) (hr : 0 < r)
    {z : ℝ} (hz : 0 < z) (size : ℝ) :
    (log size + r * log z) / (n * z) ≤ blockValue n r size := by
  apply (div_le_iff₀ (mul_pos (by positivity) hz)).mpr
  have h := log_weight_le_root (by positivity : (0 : ℝ) < r) hz size
  dsimp [blockValue]
  calc
    log size + r * log z ≤ r * exp (log size / r - 1) * z := h
    _ = r * exp (log size / r - 1) / n * (n * z) := by
      have hn0 : (n : ℝ) ≠ 0 := by positivity
      field_simp

theorem choose_mul_pow_le_exp {n r : ℕ} (hr : r ≤ n) {z : ℝ} (hz : 0 ≤ z) :
    (n.choose r : ℝ) * z ^ r ≤ exp (n * z) := by
  have hterm : z ^ r * (n.choose r : ℝ) ≤ (z + 1) ^ n := by
    rw [add_pow]
    have h := Finset.single_le_sum
      (f := fun i => z ^ i * (1 : ℝ) ^ (n - i) * n.choose i)
      (fun i _ => by positivity) (Finset.mem_range.mpr (by omega : r < n + 1))
    simpa using h
  calc
    (n.choose r : ℝ) * z ^ r ≤ (z + 1) ^ n := by simpa [mul_comm] using hterm
    _ ≤ (exp z) ^ n := pow_le_pow_left₀ (by positivity) (add_one_le_exp z) n
    _ = exp (n * z) := (exp_nat_mul z n).symm

theorem log_M_weight_le {k n r : ℕ} (hk : 3 ≤ k) (hr : r ≤ n)
    {z : ℝ} (hz : 0 < z) : log (M k n r) + r * log z ≤ n * z := by
  have hM : (0 : ℝ) < M k n r := by exact_mod_cast M_pos hk hr
  rw [← log_pow, ← log_mul hM.ne' (pow_pos hz _).ne']
  apply (log_le_iff_le_exp (mul_pos hM (pow_pos hz _))).mpr
  exact (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (M_le_choose k n r))
    (pow_nonneg hz.le _)).trans (choose_mul_pow_le_exp hr hz.le)

theorem blockValue_le_one {k n r : ℕ} (hk : 3 ≤ k) (hn : 0 < n)
    (hr : 0 < r) (hrn : r ≤ n) : blockValue n r (M k n r) ≤ 1 := by
  rw [blockValue_eq_log_weight hn hr]
  exact (div_le_one (mul_pos (by positivity) (exp_pos _))).mpr
    (log_M_weight_le hk hrn (exp_pos _))

end Erdos856b
