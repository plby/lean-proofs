import ErdosProblems.Erdos633b.GroupTwoDoubleAlgebra

/-! Rationality forced by two genuine perimeter equations and a positive
boundary coefficient for the undoubled sixty-degree group-2 shape. -/

namespace Erdos633b

theorem groupTwoSixty_rational_parameters {x y k : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hconic : x ^ 2 + x * y + y ^ 2 = 1) (M L : ℤ) (hMp : 0 < M) (hLp : 0 < L)
    (hM : (M : ℝ) * (1 + x - y) = k * (2 * x + y - 1))
    (hL : (L : ℝ) * (1 - x + y) = k * (2 * x + y + 1)) :
    IsRational x ∧ ∃ K : ℝ, IsRational K ∧ k = K * y := by
  have hcross : 3 * x * (((L : ℝ) + M) * x - ((L : ℝ) - M)) = 0 := by
    linear_combination (2 * x + y + 1) * hM - (2 * x + y - 1) * hL +
      ((L : ℝ) + M) * hconic
  have he : ((L : ℝ) + M) * x - ((L : ℝ) - M) = 0 :=
    (mul_eq_zero.mp hcross).resolve_left (mul_ne_zero (by norm_num) hx.ne')
  have hMr : (0 : ℝ) < M := by exact_mod_cast hMp
  have hLr : (0 : ℝ) < L := by exact_mod_cast hLp
  have hd : (0 : ℝ) < (L : ℝ) + M := by positivity
  have hxr : IsRational x := by
    refine ⟨((L : ℚ) - M) / ((L : ℚ) + M), ?_⟩
    push_cast
    apply (div_eq_iff hd.ne').mpr
    linarith
  have hx1 : x < 1 := by nlinarith [sq_nonneg y, mul_pos hx hy]
  have hy1 : y < 1 := by nlinarith [sq_nonneg x, mul_pos hx hy]
  have hp : 0 < 1 + x - y := by linarith
  have hm : 1 - x ≠ 0 := by linarith
  refine ⟨hxr, (M : ℝ) / (1 - x),
    (IsRational.intCast M).div ((show IsRational (1 : ℝ) from ⟨1, by norm_num⟩).sub hxr), ?_⟩
  apply mul_right_cancel₀ hm
  rw [div_mul_eq_mul_div, div_mul_cancel₀ _ hm]
  apply mul_right_cancel₀ hp.ne'
  linear_combination -y * hM - k * hconic

/-- If a rational multiple of an irrational side is a boundary length,
all contributions from a positive rational side and from the unit side
must vanish. -/
theorem pure_boundary_of_irrational_ratio {x y K : ℝ} (hx : 0 < x)
    (hxr : IsRational x) (hKr : IsRational K) (hyr : ¬ IsRational y)
    (p q r : ℕ) (he : K * y = p * x + q * y + r) : p = 0 ∧ r = 0 := by
  have hz : K - (q : ℝ) = 0 := by
    by_contra hn
    apply hyr
    have hy : y = ((p : ℝ) * x + r) / (K - q) := by
      apply (eq_div_iff hn).mpr
      linarith
    rw [hy]
    exact (((IsRational.natCast p).mul hxr).add (IsRational.natCast r)).div
      (hKr.sub (IsRational.natCast q))
  have hzero : (p : ℝ) * x + r = 0 := by linear_combination -he + y * hz
  have hp : (p : ℝ) * x = 0 := by
    have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg _
    have hp : (0 : ℝ) ≤ p := Nat.cast_nonneg _
    nlinarith
  have hp0 : (p : ℝ) = 0 := (mul_eq_zero.mp hp).resolve_right hx.ne'
  have hr0 : (r : ℝ) = 0 := by rw [hp0, zero_mul, zero_add] at hzero; exact hzero
  exact ⟨by exact_mod_cast hp0, by exact_mod_cast hr0⟩

end Erdos633b
