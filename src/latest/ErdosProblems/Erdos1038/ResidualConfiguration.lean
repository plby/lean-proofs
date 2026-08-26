import Mathlib

/-!
# Normalized finite residual configurations

This is the finite model obtained after endpoint normalization: an atom of
relative mass `k` at zero and a probability-weighted residual family in
`[1,2]`.  Because `Real.log 0 = 0` in Lean, the negative set is explicitly
augmented by its pole locations.  The main result proves the universal
endpoint window `(1 - sqrt 2, 1)` and its resulting length lower bound.
-/

open scoped ENNReal Real BigOperators
open Set MeasureTheory

namespace Erdos1038

noncomputable section

structure ResidualConfiguration (ι : Type*) [Fintype ι] where
  weight : ι → ℝ
  weight_pos : ∀ i, 0 < weight i
  sum_weight : ∑ i, weight i = 1
  location : ι → ℝ
  location_mem : ∀ i, location i ∈ Icc (1 : ℝ) 2

def residualPotential {ι : Type*} [Fintype ι]
    (C : ResidualConfiguration ι) (k x : ℝ) : ℝ :=
  k * Real.log |x| + ∑ i, C.weight i * Real.log |x - C.location i|

def residualNegativeWithPoles {ι : Type*} [Fintype ι]
    (C : ResidualConfiguration ι) (k : ℝ) : Set ℝ :=
  {x | x = 0 ∨ (∃ i, x = C.location i) ∨ residualPotential C k x < 0}

theorem residual_log_sum_le_right {ι : Type*} [Fintype ι]
    (C : ResidualConfiguration ι) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    ∑ i, C.weight i * Real.log |x - C.location i| ≤ Real.log (2 - x) := by
  calc
    ∑ i, C.weight i * Real.log |x - C.location i| ≤
        ∑ i, C.weight i * Real.log (2 - x) := by
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_left _ (C.weight_pos i).le
      have hd := C.location_mem i
      have hd1 := hd.1
      have hd2 := hd.2
      have hx0 := hx.1
      have hx1 := hx.2
      have hdx : 0 < C.location i - x := by linarith
      have habs : |x - C.location i| = C.location i - x := by
        rw [abs_of_neg (by linarith)]
        ring
      rw [habs]
      exact Real.strictMonoOn_log.monotoneOn hdx
        (by linarith : 0 < 2 - x) (by linarith)
    _ = Real.log (2 - x) := by rw [← Finset.sum_mul, C.sum_weight, one_mul]

theorem residualPotential_neg_on_Ioo_zero_one {ι : Type*} [Fintype ι]
    (C : ResidualConfiguration ι) {k x : ℝ} (hk : 1 ≤ k)
    (hx : x ∈ Ioo (0 : ℝ) 1) :
    residualPotential C k x < 0 := by
  have hlogx : Real.log x < 0 := Real.log_neg hx.1 hx.2
  have hklog : k * Real.log x ≤ Real.log x := by
    nlinarith [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hk) hlogx.le]
  have hsum := residual_log_sum_le_right C hx
  have htwo : 0 < 2 - x := by linarith [hx.2]
  have hprodpos : 0 < x * (2 - x) := mul_pos hx.1 htwo
  have hprodlt : x * (2 - x) < 1 := by
    nlinarith [sq_pos_of_pos (sub_pos.mpr hx.2)]
  have hlogprod : Real.log (x * (2 - x)) < 0 :=
    Real.log_neg hprodpos hprodlt
  have hadd : Real.log x + Real.log (2 - x) = Real.log (x * (2 - x)) := by
    rw [Real.log_mul hx.1.ne' htwo.ne']
  rw [residualPotential, abs_of_pos hx.1]
  linarith

theorem residual_log_sum_le_left {ι : Type*} [Fintype ι]
    (C : ResidualConfiguration ι) {r : ℝ} (hr : 0 < r) :
    ∑ i, C.weight i * Real.log |(-r) - C.location i| ≤ Real.log (2 + r) := by
  calc
    ∑ i, C.weight i * Real.log |(-r) - C.location i| ≤
        ∑ i, C.weight i * Real.log (2 + r) := by
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_left _ (C.weight_pos i).le
      have hd := C.location_mem i
      have hd1 := hd.1
      have hd2 := hd.2
      have habs : |(-r) - C.location i| = C.location i + r := by
        rw [abs_of_neg (by linarith)]
        ring
      rw [habs]
      have hlocpos : 0 < C.location i + r := by linarith [hd1, hr]
      have htwopos : 0 < 2 + r := by linarith [hr]
      have hle : C.location i + r ≤ 2 + r := by linarith [hd2]
      exact Real.strictMonoOn_log.monotoneOn hlocpos htwopos hle
    _ = Real.log (2 + r) := by rw [← Finset.sum_mul, C.sum_weight, one_mul]

theorem residualPotential_neg_on_left_window {ι : Type*} [Fintype ι]
    (C : ResidualConfiguration ι) {k r : ℝ} (hk : 1 ≤ k)
    (hr : r ∈ Ioo (0 : ℝ) (Real.sqrt 2 - 1)) :
    residualPotential C k (-r) < 0 := by
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrtSq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsqrtlt : Real.sqrt 2 < 2 := by nlinarith
  have hr1 : r < 1 := by linarith [hr.2, hsqrtlt]
  have hlogr : Real.log r < 0 := Real.log_neg hr.1 hr1
  have hklog : k * Real.log r ≤ Real.log r := by
    nlinarith [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hk) hlogr.le]
  have hsum := residual_log_sum_le_left C hr.1
  have htwo : 0 < 2 + r := by linarith [hr.1]
  have hprodpos : 0 < r * (2 + r) := mul_pos hr.1 htwo
  have hsquare : (r + 1) ^ 2 < (Real.sqrt 2) ^ 2 := by
    have hdiff : 0 < Real.sqrt 2 - (r + 1) := by linarith [hr.2]
    have hsumpos : 0 < Real.sqrt 2 + (r + 1) := by linarith [hsqrt, hr.1]
    nlinarith [mul_pos hdiff hsumpos]
  have hprodlt : r * (2 + r) < 1 := by nlinarith
  have hlogprod : Real.log (r * (2 + r)) < 0 :=
    Real.log_neg hprodpos hprodlt
  have hadd : Real.log r + Real.log (2 + r) = Real.log (r * (2 + r)) := by
    rw [Real.log_mul hr.1.ne' htwo.ne']
  rw [residualPotential, abs_neg, abs_of_pos hr.1]
  linarith

theorem endpointWindow_subset_residualNegativeWithPoles
    {ι : Type*} [Fintype ι] (C : ResidualConfiguration ι)
    {k : ℝ} (hk : 1 ≤ k) :
    Ioo (1 - Real.sqrt 2) 1 ⊆ residualNegativeWithPoles C k := by
  intro x hx
  change x = 0 ∨ (∃ i, x = C.location i) ∨ residualPotential C k x < 0
  rcases lt_trichotomy x 0 with hxneg | rfl | hxpos
  · right
    right
    have hxlow := hx.1
    have hr : -x ∈ Ioo (0 : ℝ) (Real.sqrt 2 - 1) := by
      constructor <;> linarith
    simpa only [neg_neg] using! residualPotential_neg_on_left_window C hk hr
  · exact Or.inl rfl
  · right
    right
    exact residualPotential_neg_on_Ioo_zero_one C hk ⟨hxpos, hx.2⟩

theorem endpointWindow_volume_le {ι : Type*} [Fintype ι]
    (C : ResidualConfiguration ι) {k : ℝ} (hk : 1 ≤ k) :
    ENNReal.ofReal (Real.sqrt 2) ≤ volume (residualNegativeWithPoles C k) := by
  have hmono : volume (Ioo (1 - Real.sqrt 2) 1) ≤
      volume (residualNegativeWithPoles C k) :=
    measure_mono (endpointWindow_subset_residualNegativeWithPoles C hk)
  rw [Real.volume_Ioo] at hmono
  simpa [show (1 : ℝ) - (1 - Real.sqrt 2) = Real.sqrt 2 by ring] using! hmono

end

end Erdos1038
