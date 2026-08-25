import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Tactic

/-!
# Weighted Hölder in the integer-power form for Burgess amplification
-/

namespace Pollack17.Burgess

open scoped BigOperators

theorem weighted_power_sum_le {ι : Type*} (S : Finset ι) (w z : ι → ℝ)
    (hw : ∀ i ∈ S, 0 ≤ w i) (hz : ∀ i ∈ S, 0 ≤ z i) (k : ℕ) :
    (∑ i ∈ S, w i * z i) ^ (k + 1) ≤
      (∑ i ∈ S, w i) ^ k * ∑ i ∈ S, w i * z i ^ (k + 1) := by
  let W := ∑ i ∈ S, w i
  have hW0 : 0 ≤ W := Finset.sum_nonneg hw
  by_cases hW : W = 0
  · have hwi : ∀ i ∈ S, w i = 0 := (Finset.sum_eq_zero_iff_of_nonneg hw).mp hW
    have hleft : (∑ i ∈ S, w i * z i) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [hwi i hi, zero_mul]
    have hright : (∑ i ∈ S, w i * z i ^ (k + 1)) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [hwi i hi, zero_mul]
    simp [hleft, hright]
  have hWpos : 0 < W := lt_of_le_of_ne hW0 (Ne.symm hW)
  have hj := Real.pow_arith_mean_le_arith_mean_pow S (fun i => w i / W) z
    (fun i hi => div_nonneg (hw i hi) hW0)
    (by rw [← Finset.sum_div]; exact div_self hW) hz (k + 1)
  have hj' : ((∑ i ∈ S, w i * z i) / W) ^ (k + 1) ≤
      (∑ i ∈ S, w i * z i ^ (k + 1)) / W := by
    simpa only [div_mul_eq_mul_div, ← Finset.sum_div] using hj
  rw [div_pow] at hj'
  have hscaled := (div_le_iff₀ (pow_pos hWpos (k + 1))).mp hj'
  calc
    (∑ i ∈ S, w i * z i) ^ (k + 1) ≤
        ((∑ i ∈ S, w i * z i ^ (k + 1)) / W) * W ^ (k + 1) := hscaled
    _ = W ^ k * ∑ i ∈ S, w i * z i ^ (k + 1) := by
      rw [pow_succ]
      field_simp
    _ = _ := rfl

theorem weighted_even_power_sum_le {ι : Type*} (S : Finset ι) (w z : ι → ℝ)
    (hw : ∀ i ∈ S, 0 ≤ w i) (hz : ∀ i ∈ S, 0 ≤ z i) (k : ℕ) :
    (∑ i ∈ S, w i * z i) ^ (2 * (k + 1)) ≤
      (∑ i ∈ S, w i) ^ (2 * k) * (∑ i ∈ S, w i ^ 2) *
        ∑ i ∈ S, z i ^ (2 * (k + 1)) := by
  have hsum0 : 0 ≤ ∑ i ∈ S, w i * z i :=
    Finset.sum_nonneg fun i hi => mul_nonneg (hw i hi) (hz i hi)
  have hj := weighted_power_sum_le S w z hw hz k
  have hj2 := pow_le_pow_left₀ (pow_nonneg hsum0 _) hj 2
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq S w (fun i => z i ^ (k + 1))
  have hpowers (i : ι) : (z i ^ (k + 1)) ^ 2 = z i ^ (2 * (k + 1)) := by
    rw [← pow_mul]
    congr 1
    omega
  simp_rw [hpowers] at hcs
  calc
    (∑ i ∈ S, w i * z i) ^ (2 * (k + 1)) =
        ((∑ i ∈ S, w i * z i) ^ (k + 1)) ^ 2 := by
      rw [← pow_mul]
      congr 1
      omega
    _ ≤ ((∑ i ∈ S, w i) ^ k * ∑ i ∈ S, w i * z i ^ (k + 1)) ^ 2 := hj2
    _ = (∑ i ∈ S, w i) ^ (2 * k) * (∑ i ∈ S, w i * z i ^ (k + 1)) ^ 2 := by
      rw [mul_pow, ← pow_mul]
      congr 2
      omega
    _ ≤ (∑ i ∈ S, w i) ^ (2 * k) *
        ((∑ i ∈ S, w i ^ 2) * ∑ i ∈ S, z i ^ (2 * (k + 1))) :=
      mul_le_mul_of_nonneg_left hcs (pow_nonneg (Finset.sum_nonneg hw) _)
    _ = _ := by ring

end Pollack17.Burgess
