import ErdosProblems.Erdos1148.PowerSumRegularization
import ErdosProblems.Erdos1148.RealDirichletValue
import Mathlib.Algebra.Order.Floor.Ring

/-! # Real cutoffs for power sums and nonprincipal Dirichlet series -/

namespace Erdos1148.DukeArithmetic

open MeasureTheory Set

lemma rpow_integral_short_interval_bounds {s x y : ℝ}
    (hs : 0 < s) (hs1 : s < 1) (hx : 0 < x) (hxy : x ≤ y) (hyx : y ≤ x + 1) :
    0 ≤ (y ^ (1 - s) - x ^ (1 - s)) / (1 - s) ∧
      (y ^ (1 - s) - x ^ (1 - s)) / (1 - s) ≤ x ^ (-s) := by
  have hi : (∫ t : ℝ in x..y, t ^ (-s)) =
      (y ^ (1 - s) - x ^ (1 - s)) / (1 - s) := by
    rw [integral_rpow (Or.inl (by linarith : -1 < -s))]
    rw [show -s + 1 = 1 - s by ring]
  rw [← hi]
  constructor
  · exact intervalIntegral.integral_nonneg hxy (fun t ht =>
      Real.rpow_nonneg (hx.le.trans ht.1) _)
  · have hint : IntervalIntegrable (fun t : ℝ => t ^ (-s)) volume x y :=
      intervalIntegral.intervalIntegrable_rpow
        (Or.inr (notMem_uIcc_of_lt hx (hx.trans_le hxy)))
    calc
      _ ≤ ∫ _ : ℝ in x..y, x ^ (-s) :=
        intervalIntegral.integral_mono_on hxy hint intervalIntegrable_const
          (fun t ht => Real.rpow_le_rpow_of_nonpos hx ht.1 (neg_nonpos.mpr hs.le))
      _ = (y - x) * x ^ (-s) := by rw [intervalIntegral.integral_const, smul_eq_mul]
      _ ≤ 1 * x ^ (-s) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = _ := one_mul _

theorem power_sum_regularized_floor_error_le {s : ℝ} (hs : 0 < s) (hs1 : s < 1)
    {x : ℝ} (hx : 1 ≤ x) :
    |(∑ k ∈ Finset.range ⌊x⌋₊, (k + 1 : ℝ) ^ (-s)) -
        (realZetaRegularized s + x ^ (1 - s) / (1 - s))| ≤ 2 * x ^ (-s) := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hfloor := Nat.floor_le hx0.le
  have hceil := (Nat.lt_floor_add_one x).le
  have hb := power_sum_regularized_error_le hs hs1 ⌊x⌋₊
  have hp : (⌊x⌋₊ + 1 : ℝ) ^ (-s) ≤ x ^ (-s) :=
    Real.rpow_le_rpow_of_nonpos hx0 hceil (neg_nonpos.mpr hs.le)
  have hi := rpow_integral_short_interval_bounds hs hs1 hx0 hceil
    (by linarith : (⌊x⌋₊ : ℝ) + 1 ≤ x + 1)
  calc
    _ ≤ |(∑ k ∈ Finset.range ⌊x⌋₊, (k + 1 : ℝ) ^ (-s)) -
          (realZetaRegularized s + (⌊x⌋₊ + 1 : ℝ) ^ (1 - s) / (1 - s))| +
        |(realZetaRegularized s + (⌊x⌋₊ + 1 : ℝ) ^ (1 - s) / (1 - s)) -
          (realZetaRegularized s + x ^ (1 - s) / (1 - s))| := abs_sub_le _ _ _
    _ ≤ x ^ (-s) + x ^ (-s) := by
      apply add_le_add (hb.trans hp)
      rw [show (realZetaRegularized s + (⌊x⌋₊ + 1 : ℝ) ^ (1 - s) / (1 - s)) -
          (realZetaRegularized s + x ^ (1 - s) / (1 - s)) =
          ((⌊x⌋₊ + 1 : ℝ) ^ (1 - s) - x ^ (1 - s)) / (1 - s) by ring,
        abs_of_nonneg hi.1]
      exact hi.2
    _ = _ := by ring

theorem realDirichletValue_sub_floor_partialSum_norm_le {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℝ q) (hχ : χ ≠ 1) {s : ℝ} (hs : 0 < s)
    {x : ℝ} (hx : 0 < x) :
    ‖realDirichletValue χ s - realDirichletPartialSum χ s ⌊x⌋₊‖ ≤
      2 * q * x ^ (-s) := by
  have h := realDirichletValue_sub_partialSum_norm_le χ hχ hs ⌊x⌋₊
  simp only [Nat.cast_add, Nat.cast_one] at h
  exact h.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_nonpos hx (Nat.lt_floor_add_one x).le
      (neg_nonpos.mpr hs.le)) (by positivity))

end Erdos1148.DukeArithmetic
