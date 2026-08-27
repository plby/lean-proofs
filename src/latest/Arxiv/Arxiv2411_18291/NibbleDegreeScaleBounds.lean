import Arxiv.Arxiv2411_18291.NibbleComparisons

/-! # Uniform degree-error bounds from scalar nibble parameters -/

namespace Arxiv2411_18291

theorem nibbleEdgeScale_ge_width {a D p : ℝ} (hD : 0 ≤ D) (hp : 0 < p) (hp1 : p ≤ 1) :
    a ^ 2 * D ≤ nibbleEdgeScale a D p := by
  unfold nibbleEdgeScale
  apply (le_div_iff₀ hp).mpr
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hp1 (mul_nonneg (sq_nonneg a) hD)

theorem nibbleDegreeError_nonneg (k : ℕ) {a D p : ℝ} (hD : 0 ≤ D) (hp : 0 ≤ p) :
    0 ≤ nibbleDegreeError k a D p := by
  unfold nibbleDegreeError
  exact mul_nonneg (by positivity) (nibbleEdgeScale_nonneg hD hp)

theorem nibbleEdgeScale_le_scaled_main {k : ℕ} (hk : 0 < k) {a D p : ℝ}
    (ha : 0 ≤ a) (hD : 0 < D) (hp : 0 < p) (hap : a ≤ p ^ k) :
    nibbleEdgeScale a D p ≤ a * nibbleDegreeMain k D p := by
  apply (div_le_iff₀ (nibbleDegreeMain_pos hD hp)).mp
  rw [nibbleEdgeScale_degree_ratio hk hD.ne' hp.ne']
  apply (div_le_iff₀ (pow_pos hp k)).mpr
  simpa only [pow_two] using mul_le_mul_of_nonneg_left hap ha

theorem nibbleEdgeScale_le_main {k : ℕ} (hk : 0 < k) {a D p : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hD : 0 < D) (hp : 0 < p) (hap : a ≤ p ^ k) :
    nibbleEdgeScale a D p ≤ nibbleDegreeMain k D p := by
  calc
    _ ≤ a * nibbleDegreeMain k D p := nibbleEdgeScale_le_scaled_main hk ha hD hp hap
    _ ≤ 1 * nibbleDegreeMain k D p :=
      mul_le_mul_of_nonneg_right ha1 (nibbleDegreeMain_pos hD hp).le
    _ = _ := one_mul _

theorem nibbleDegreeError_le_scaled_main {k : ℕ} (hk : 0 < k) {a D p : ℝ}
    (ha : 0 ≤ a) (hD : 0 < D) (hp : 0 < p) (hap : a ≤ p ^ k) :
    nibbleDegreeError k a D p ≤ (16 * (k : ℝ) * a) * nibbleDegreeMain k D p := by
  have h := mul_le_mul_of_nonneg_left (nibbleEdgeScale_le_scaled_main hk ha hD hp hap)
    (show 0 ≤ 16 * (k : ℝ) by positivity)
  simpa only [nibbleDegreeError, mul_assoc] using h

theorem nibbleDegreeError_sq_le {k : ℕ} (hk : 0 < k) {a D p : ℝ}
    (ha : 0 ≤ a) (hD : 0 < D) (hp : 0 < p) (hap : a ≤ p ^ k)
    (hsmall : (16 * (k : ℝ)) ^ 2 * a ≤ 1) :
    nibbleDegreeError k a D p ^ 2 ≤ nibbleEdgeScale a D p * nibbleDegreeMain k D p := by
  have ht := nibbleEdgeScale_le_scaled_main hk ha hD hp hap
  have ht0 := nibbleEdgeScale_nonneg (a := a) hD.le hp.le
  have hm0 := (nibbleDegreeMain_pos (k := k) hD hp).le
  have hmul := mul_le_mul_of_nonneg_left ht (mul_nonneg (sq_nonneg (16 * (k : ℝ))) ht0)
  have hs := mul_le_mul_of_nonneg_right hsmall (mul_nonneg ht0 hm0)
  unfold nibbleDegreeError
  nlinarith only [hmul, hs]

theorem nibbleDegreeError_le_main {k : ℕ} (hk : 0 < k) {a D p : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hD : 0 < D) (hp : 0 < p) (hap : a ≤ p ^ k)
    (hsmall : (16 * (k : ℝ)) ^ 2 * a ≤ 1) :
    nibbleDegreeError k a D p ≤ nibbleDegreeMain k D p := by
  have hu2 := nibbleDegreeError_sq_le hk ha hD hp hap hsmall
  have ht := nibbleEdgeScale_le_main hk ha ha1 hD hp hap
  have hm0 := (nibbleDegreeMain_pos (k := k) hD hp).le
  have htm := mul_le_mul_of_nonneg_right ht hm0
  have hu0 := nibbleDegreeError_nonneg k (a := a) hD.le hp.le
  nlinarith only [hu2, htm, hu0, hm0]

end Arxiv2411_18291
