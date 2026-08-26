import ErdosProblems.Erdos633b.RationalTilingSineSigns

/-! Exact conjugate sine-product identity for the first group-1 outer
shape. The proof is polynomial and does not divide by any sine or cosine. -/

namespace Erdos633b

theorem odd_sin_pi_sub (k : ℕ) (hk : Odd k) (x : ℝ) :
    Real.sin (k * Real.pi - x) = Real.sin x := by
  rw [Real.sin_sub, Real.sin_nat_mul_pi, Real.cos_nat_mul_pi, hk.neg_one_pow]
  ring

theorem odd_cos_pi_sub (k : ℕ) (hk : Odd k) (x : ℝ) :
    Real.cos (k * Real.pi - x) = -Real.cos x := by
  rw [Real.cos_sub, Real.sin_nat_mul_pi, Real.cos_nat_mul_pi, hk.neg_one_pow]
  ring

theorem groupOne_first_sine_product (k : ℕ) (hk : Odd k) (x y z : ℝ)
    (hs : x + y + z = k * Real.pi) (hr : 3 * x + 2 * y = k * Real.pi) :
    Real.sin x * Real.sin (2 * x) * Real.sin (2 * y) =
      (4 * Real.cos x * (1 - Real.cos x) * (1 + 2 * Real.cos x)) *
        (Real.sin x * Real.sin y * Real.sin z) := by
  have hy : 2 * y = k * Real.pi - 3 * x := by linarith
  have hyzsub : y - z = -(2 * x) := by linarith
  have hyzadd : y + z = k * Real.pi - x := by linarith
  have hsin : Real.sin (2 * y) = Real.sin (3 * x) := by rw [hy, odd_sin_pi_sub k hk]
  have hp := Real.cos_sub y z
  have hm := Real.cos_add y z
  rw [hyzsub, Real.cos_neg] at hp
  rw [hyzadd, odd_cos_pi_sub k hk] at hm
  have hpair : 2 * Real.sin y * Real.sin z = 2 * Real.cos x ^ 2 + Real.cos x - 1 := by
    rw [Real.cos_two_mul] at hp
    linarith
  rw [Real.sin_two_mul, hsin, Real.sin_three_mul]
  linear_combination
    -(2 * Real.sin x * Real.cos x * (1 - Real.cos x) * (1 + 2 * Real.cos x)) * hpair +
    (2 * Real.sin x * Real.cos x * (-4 * Real.sin x ^ 2 + 4 * Real.cos x ^ 2 - 1)) *
      Real.sin_sq_add_cos_sq x

theorem groupOne_first_sine_product_nonpos (k : ℕ) (hk : Odd k) (x y z : ℝ)
    (hs : x + y + z = k * Real.pi) (hr : 3 * x + 2 * y = k * Real.pi)
    (hc0 : Real.cos x < 0) (hc1 : -(1 / 2 : ℝ) < Real.cos x) :
    (Real.sin x * Real.sin y * Real.sin z) *
      (Real.sin x * Real.sin (2 * x) * Real.sin (2 * y)) ≤ 0 := by
  rw [groupOne_first_sine_product k hk x y z hs hr]
  have hcoef : 4 * Real.cos x * (1 - Real.cos x) * (1 + 2 * Real.cos x) < 0 :=
    mul_neg_of_neg_of_pos
      (mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by norm_num) hc0) (by linarith))
      (by linarith)
  have hh := mul_nonpos_of_nonpos_of_nonneg hcoef.le
    (sq_nonneg (Real.sin x * Real.sin y * Real.sin z))
  convert hh using 1 <;> first | rfl | ring

end Erdos633b
