import ErdosProblems.Erdos490.Rectangles
import ErdosProblems.Erdos490.Series

noncomputable section
namespace Erdos490
open Finset BigOperators
set_option maxHeartbeats 800000

def rectangleCap (k : ℕ) : ℝ := (4/5) / (geometricRatio^(k+1))^2

def rectangleMultiplicity (k : ℕ) : ℕ :=
  if k < 16 then N_layer 2 k else min (N_layer 2 k) ⌊rectangleCap k⌋₊

lemma rectangleMultiplicity_le (k : ℕ) : rectangleMultiplicity k ≤ N_layer 2 k := by
  unfold rectangleMultiplicity
  split_ifs
  · rfl
  · exact min_le_left _ _

lemma rectangleMultiplicity_active (k : ℕ) (hk : rectangleMultiplicity k < N_layer 2 k) :
    16 ≤ k ∧ rectangleMultiplicity k = ⌊rectangleCap k⌋₊ := by
  have h16 : ¬ k < 16 := by intro h; simpa [rectangleMultiplicity, h] using hk
  refine ⟨by omega, ?_⟩
  simp only [rectangleMultiplicity, if_neg h16] at hk ⊢
  exact min_eq_right (by omega)

lemma floor_inverse_sqrt_bound (x : ℝ) (hx : 0 < x) :
    1 / Real.sqrt ((⌊(4/5 : ℝ)/x^2⌋₊ : ℝ)+1) ≤ (1119/1000 : ℝ)*x := by
  have hs : 0 < Real.sqrt ((⌊(4/5 : ℝ)/x^2⌋₊ : ℝ)+1) := by positivity
  apply (div_le_iff₀ hs).mpr
  apply (sq_le_sq₀ zero_le_one (by positivity)).mp
  rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
  have hf := Nat.lt_floor_add_one ((4/5 : ℝ)/x^2)
  have hh := mul_lt_mul_of_pos_right hf (sq_pos_of_pos hx)
  rw [div_mul_cancel₀ _ (sq_pos_of_pos hx).ne'] at hh
  nlinarith

lemma rectangle_weight_majorant (k : ℕ) :
    rectangleWeight rectangleMultiplicity rectangleGrowth k * (N_layer 2 k : ℝ) ≤
      ((72/100 : ℝ)*(1119/1000))*weightedGeometricTail k := by
  by_cases hk : rectangleMultiplicity k < N_layer 2 k
  · obtain ⟨h16, heq⟩ := rectangleMultiplicity_active k hk
    have hd := dyadic_density_bound k h16
    have hs := floor_inverse_sqrt_bound (geometricRatio^(k+1))
      (pow_pos geometricRatio_pos _)
    have hY : 0 < Y_val 2 k := by rw [Y_val_two]; exact_mod_cast dyadicScale_pos k
    have hM : 0 < M_layer 2 k := M_layer_positive _ _
    have hg : 0 ≤ rectangleGrowth k := zero_le_one.trans (rectangleGrowth_ge_one k)
    calc
      _ = ((N_layer 2 k : ℝ)/(Y_val 2 k*Real.sqrt (M_layer 2 k))) *
          (1/Real.sqrt ((⌊rectangleCap k⌋₊ : ℝ)+1)) * rectangleGrowth k := by
        rw [rectangleWeight, if_pos hk, heq]
        ring
      _ ≤ (72/100 : ℝ)*((1119/1000)*geometricRatio^(k+1))*rectangleGrowth k := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul hd hs (by positivity) (by norm_num)) hg
      _ = _ := by rw [weightedGeometricTail, if_pos h16]; ring
  · simp only [rectangleWeight, if_neg hk, zero_mul]
    exact mul_nonneg (by norm_num) (weightedGeometricTail_nonneg k)

lemma rectangle_weights_summable : Summable (fun k =>
    rectangleWeight rectangleMultiplicity rectangleGrowth k * (N_layer 2 k : ℝ)) := by
  apply (weightedGeometricTail_hasSum.summable.mul_left ((72/100 : ℝ)*(1119/1000))).of_nonneg_of_le
  · intro k
    exact mul_nonneg (rectangleWeight_nonneg _ _
      (fun k => zero_le_one.trans (rectangleGrowth_ge_one k)) k) (Nat.cast_nonneg _)
  · exact rectangle_weight_majorant

lemma rectangle_weightTotal_lt : weightTotal
    (rectangleWeight rectangleMultiplicity rectangleGrowth) < (77/1000 : ℝ) := by
  have h := Summable.tsum_le_tsum rectangle_weight_majorant rectangle_weights_summable
    (weightedGeometricTail_hasSum.summable.mul_left ((72/100 : ℝ)*(1119/1000)))
  rw [tsum_mul_left] at h
  have ht := mul_lt_mul_of_pos_left weightedGeometricTail_sum_lt
    (by norm_num : 0 < (72/100 : ℝ)*(1119/1000))
  dsimp [weightTotal]
  linarith

end Erdos490
