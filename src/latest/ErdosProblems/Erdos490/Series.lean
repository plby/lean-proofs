import Mathlib

noncomputable section
namespace Erdos490
open Finset BigOperators Filter
open scoped Topology
set_option maxHeartbeats 800000

/-- A rational upper bound for the reciprocal cube root of two. -/
def geometricRatio : ℝ := 79371 / 100000

def rectangleGrowth (k : ℕ) : ℝ := 1 + ((k - 100 : ℕ) : ℝ)

lemma geometricRatio_pos : 0 < geometricRatio := by norm_num [geometricRatio]
lemma geometricRatio_lt_one : geometricRatio < 1 := by norm_num [geometricRatio]
lemma geometricRatio_cube : 1 ≤ 2 * geometricRatio^3 := by norm_num [geometricRatio]

lemma rectangleGrowth_ge_one (k : ℕ) : 1 ≤ rectangleGrowth k := by
  unfold rectangleGrowth
  exact le_add_of_nonneg_right (Nat.cast_nonneg _)

lemma rectangleGrowth_tendsto : Tendsto rectangleGrowth atTop atTop := by
  apply tendsto_atTop_mono' atTop (show ∀ᶠ k : ℕ in atTop,
    (k : ℝ) - 100 ≤ rectangleGrowth k from ?_)
    (show Tendsto (fun k : ℕ => (k : ℝ)-100) atTop atTop from
      tendsto_atTop_add_const_right atTop (-100) tendsto_natCast_atTop_atTop)
  filter_upwards [eventually_ge_atTop 100] with k hk
  simp only [rectangleGrowth, Nat.cast_sub hk, Nat.cast_ofNat]
  linarith

lemma geometric_tail_hasSum (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (K : ℕ) :
    HasSum (fun k : ℕ => if K ≤ k then q^(k+1) else 0) (q^(K+1) / (1-q)) := by
  let f := fun k : ℕ => if K ≤ k then q^(k+1) else 0
  have hshift : HasSum (fun k => f (k+K)) (q^(K+1)/(1-q)) := by
    have heq : (fun k => f (k+K)) = (fun k => q^(K+1)*q^k) := by
      funext k
      dsimp [f]
      rw [if_pos (by omega)]
      ring
    rw [heq, div_eq_mul_inv]
    exact HasSum.mul_left _ (hasSum_geometric_of_lt_one hq0 hq1)
  have hprefix : ∑ k ∈ range K, f k = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    simp [f, not_le.mpr (Finset.mem_range.mp hk)]
  simpa only [hprefix, zero_add] using hshift.sum_range_add

lemma geometric_slope_hasSum (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    HasSum (fun k : ℕ => ((k-100 : ℕ) : ℝ) * q^(k+1)) (q^102/(1-q)^2) := by
  let f := fun k : ℕ => ((k-100 : ℕ) : ℝ) * q^(k+1)
  have hq : ‖q‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hq0] using hq1
  have hone : 1-q ≠ 0 := ne_of_gt (sub_pos.mpr hq1)
  have hsum : HasSum (fun k : ℕ => ((k : ℝ)+1)*q^k) (1/(1-q)^2) := by
    have heq : (1 : ℝ)/(1-q)^2 = q/(1-q)^2+(1-q)⁻¹ := by field_simp; ring
    simp only [add_mul, one_mul, heq]
    exact (hasSum_coe_mul_geometric_of_norm_lt_one hq).add
      (hasSum_geometric_of_lt_one hq0 hq1)
  have hshift : HasSum (fun k => f (k+101)) (q^102/(1-q)^2) := by
    have heq : (fun k => f (k+101)) = (fun k : ℕ => q^102*(((k : ℝ)+1)*q^k)) := by
      funext k
      dsimp [f]
      rw [show k+101-100=k+1 by omega]
      push_cast
      ring
    rw [heq, show q^102/(1-q)^2 = q^102*(1/(1-q)^2) by ring]
    exact HasSum.mul_left _ hsum
  have hprefix : ∑ k ∈ range 101, f k = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    simp [f, Nat.sub_eq_zero_of_le (show k ≤ 100 by have := Finset.mem_range.mp hk; omega)]
  simpa only [hprefix, zero_add] using hshift.sum_range_add

def weightedGeometricTail (k : ℕ) : ℝ :=
  if 16 ≤ k then rectangleGrowth k * geometricRatio^(k+1) else 0

lemma weightedGeometricTail_hasSum : HasSum weightedGeometricTail
    (geometricRatio^17/(1-geometricRatio) + geometricRatio^102/(1-geometricRatio)^2) := by
  have heq : weightedGeometricTail = fun k =>
      (if 16 ≤ k then geometricRatio^(k+1) else 0) +
      ((k-100 : ℕ) : ℝ)*geometricRatio^(k+1) := by
    funext k
    dsimp [weightedGeometricTail, rectangleGrowth]
    split_ifs with hk
    · ring
    · simp [Nat.sub_eq_zero_of_le (show k ≤ 100 by omega)]
  rw [heq]
  exact (geometric_tail_hasSum geometricRatio geometricRatio_pos.le geometricRatio_lt_one 16).add
    (geometric_slope_hasSum geometricRatio geometricRatio_pos.le geometricRatio_lt_one)

lemma weightedGeometricTail_nonneg (k : ℕ) : 0 ≤ weightedGeometricTail k := by
  unfold weightedGeometricTail
  split_ifs
  · exact mul_nonneg (zero_le_one.trans (rectangleGrowth_ge_one k))
      (pow_nonneg geometricRatio_pos.le _)
  · rfl

lemma weightedGeometricTail_sum_lt : ∑' k, weightedGeometricTail k < (191/2000 : ℝ) := by
  rw [weightedGeometricTail_hasSum.tsum_eq]
  norm_num [geometricRatio]

end Erdos490
