import ErdosProblems.Erdos490.Parameters
import ErdosProblems.Erdos490.EulerBounds

noncomputable section
namespace Erdos490
open Finset BigOperators
set_option maxHeartbeats 800000

lemma rectangleCap_ratio (k : ℕ) : rectangleCap k / Y_val 2 k ≤
    (4/5 : ℝ)*geometricRatio^(k+1) := by
  have hY : 0 < Y_val 2 k := by rw [Y_val_two]; exact_mod_cast dyadicScale_pos k
  have hq : 0 < geometricRatio^(k+1) := pow_pos geometricRatio_pos _
  have hpow := one_le_pow₀ geometricRatio_cube (n := k+1)
  have heq : (2*geometricRatio^3)^(k+1) =
      Y_val 2 k * (geometricRatio^(k+1))^2 * geometricRatio^(k+1) := by
    rw [Y_val_two]
    simp only [dyadicScale, Nat.cast_pow, Nat.cast_ofNat, mul_pow, ← pow_mul]
    ring
  rw [heq] at hpow
  apply (div_le_iff₀ hY).mpr
  unfold rectangleCap
  apply (div_le_iff₀ (sq_pos_of_pos hq)).mpr
  nlinarith

lemma dyadic_tail_scale (k : ℕ) (hk : 16 ≤ k) : (131072 : ℝ) ≤ Y_val 2 k := by
  rw [Y_val_two]
  have h : dyadicScale 16 ≤ dyadicScale k := by
    unfold dyadicScale
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  exact_mod_cast h

lemma rectangle_log_tail_bound (k : ℕ) (hk : 16 ≤ k) :
    Real.log (E_val 2 k (rectangleMultiplicity k)) ≤
      ((4/5 : ℝ)*131072/131071)*geometricRatio^(k+1) := by
  have hY := dyadic_tail_scale k hk
  have hYpos : 0 < Y_val 2 k := by linarith
  have hden : 0 < Y_val 2 k-1 := by linarith
  have hcap : (rectangleMultiplicity k : ℝ) ≤ rectangleCap k := by
    have hm : rectangleMultiplicity k ≤ ⌊rectangleCap k⌋₊ := by
      simp only [rectangleMultiplicity, if_neg (by omega : ¬ k < 16)]
      exact min_le_right _ _
    exact (Nat.cast_le.mpr hm).trans (Nat.floor_le (by unfold rectangleCap; positivity [geometricRatio_pos]))
  have hratio : Y_val 2 k/(Y_val 2 k-1) ≤ (131072/131071 : ℝ) := by
    apply (div_le_iff₀ hden).mpr
    linarith
  calc
    _ ≤ (rectangleMultiplicity k : ℝ)/(Y_val 2 k-1) :=
      log_E_val_le _ _ _ (by linarith)
    _ ≤ rectangleCap k/(Y_val 2 k-1) := div_le_div_of_nonneg_right hcap hden.le
    _ = (rectangleCap k/Y_val 2 k)*(Y_val 2 k/(Y_val 2 k-1)) := by field_simp
    _ ≤ ((4/5 : ℝ)*geometricRatio^(k+1))*(131072/131071) :=
      mul_le_mul (rectangleCap_ratio k) hratio (by positivity) (by positivity [geometricRatio_pos])
    _ = _ := by ring

lemma geometric_shift_hasSum (K : ℕ) :
    HasSum (fun k : ℕ => geometricRatio^(k+K)) (geometricRatio^K/(1-geometricRatio)) := by
  simpa [pow_add, mul_comm, div_eq_mul_inv] using
    HasSum.mul_left (geometricRatio^K)
      (hasSum_geometric_of_lt_one geometricRatio_pos.le geometricRatio_lt_one)

lemma rectangle_log_summable : Summable (fun k => Real.log (E_val 2 k (rectangleMultiplicity k))) := by
  apply (summable_nat_add_iff 16).mp
  apply ((geometric_shift_hasSum 17).summable.mul_left ((4/5 : ℝ)*131072/131071)).of_nonneg_of_le
  · intro k
    exact Real.log_nonneg (E_val_ge_one _ _ _)
  · intro k
    simpa only [Nat.add_assoc] using rectangle_log_tail_bound (k+16) (by omega)

lemma rectangle_log_tail_sum_lt :
    ∑' k, Real.log (E_val 2 (k+16) (rectangleMultiplicity (k+16))) < (77/1000 : ℝ) := by
  have hs := (summable_nat_add_iff 16).mpr rectangle_log_summable
  have h := Summable.tsum_le_tsum
    (fun k => by simpa only [Nat.add_assoc] using rectangle_log_tail_bound (k+16) (by omega)) hs
    ((geometric_shift_hasSum 17).summable.mul_left ((4/5 : ℝ)*131072/131071))
  rw [tsum_mul_left, (geometric_shift_hasSum 17).tsum_eq] at h
  refine h.trans_lt ?_
  norm_num [geometricRatio]

lemma exp_small_bound : Real.exp (77/1000 : ℝ) < (1081/1000 : ℝ) := by
  have h := Real.exp_bound (show |(77/1000 : ℝ)| ≤ 1 by norm_num) (show 0 < 8 by norm_num)
  norm_num at h
  linarith [abs_le.mp h]

lemma rectangle_D_lt : D_val 2 rectangleMultiplicity < 23 := by
  have heq : D_val 2 rectangleMultiplicity =
      (∏ k ∈ range 16, E_val 2 k (rectangleMultiplicity k)) *
      Real.exp (∑' k, Real.log (E_val 2 (k+16) (rectangleMultiplicity (k+16)))) := by
    unfold D_val
    rw [← rectangle_log_summable.sum_add_tsum_nat_add 16, Real.exp_add, Real.exp_sum]
    congr 1
    apply Finset.prod_congr rfl
    intro k hk
    exact Real.exp_log (zero_lt_one.trans_le (E_val_ge_one _ _ _))
  rw [heq]
  have he := (Real.exp_lt_exp.mpr rectangle_log_tail_sum_lt).trans exp_small_bound
  have hp := finite_E_product_lt rectangleMultiplicity
  have h := mul_lt_mul hp he.le (Real.exp_pos _) (by norm_num : (0 : ℝ) ≤ 211/10)
  linarith

lemma exp_gamma_lt : Real.exp γ < 1785/1000 := by
  have h_exp_bound : Real.exp (579/1000 : ℝ) < 1785/1000 := by
    have h := Real.exp_bound (show |(579/1000 : ℝ)| ≤ 1 by norm_num) (show 0 < 20 by norm_num)
    norm_num at h
    linarith [abs_le.mp h]
  exact (Real.exp_le_exp.mpr (le_of_lt gamma_lt_tight)).trans_lt h_exp_bound

lemma rectangle_constant_lt :
    (111/100 : ℝ)^2 * Real.exp γ * D_val 2 rectangleMultiplicity /
      (1-weightTotal (rectangleWeight rectangleMultiplicity rectangleGrowth))^2 < 60 := by
  have hΩ := rectangle_weightTotal_lt
  have hD := rectangle_D_lt
  have hγ := exp_gamma_lt
  have hden : (1-(77/1000 : ℝ))^2 ≤
      (1-weightTotal (rectangleWeight rectangleMultiplicity rectangleGrowth))^2 := by
    nlinarith
  calc
    _ ≤ (111/100 : ℝ)^2 * Real.exp γ * D_val 2 rectangleMultiplicity / (1-77/1000)^2 :=
      div_le_div_of_nonneg_left (mul_nonneg (mul_nonneg (sq_nonneg _) (Real.exp_nonneg _))
        (Real.exp_nonneg _)) (by norm_num) hden
    _ < (111/100 : ℝ)^2 * (1785/1000) * 23 / (1-77/1000)^2 := by
      gcongr
      exact Real.exp_nonneg _
    _ < 60 := by norm_num

end Erdos490
