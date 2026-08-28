import Wikipedia.SmoothSixDPoincare.MorseBeltFaceFlow

/-!
# Exact quadratic flow from the lower annular chart to the upper chart

For a nonzero positive normal coordinate, the explicit negative time
interchanges its radius and the negative sphere direction. If the normal
radius is at most `3/2`, the entire trajectory stays in the original
controlled product block of radius `2 * ρ`.
-/

noncomputable section

open Set Metric

namespace Wikipedia.SmoothSixDPoincare.MorseHandle

def annularCrossingTime (r : ℝ) : ℝ := Real.log (r / Real.sqrt (1 + r ^ 2))

theorem exp_annularCrossingTime {r : ℝ} (hr : 0 < r) :
    Real.exp (annularCrossingTime r) = r / Real.sqrt (1 + r ^ 2) :=
  Real.exp_log (div_pos hr (Real.sqrt_pos.mpr (by positivity)))

theorem exp_neg_annularCrossingTime {r : ℝ} (hr : 0 < r) :
    Real.exp (-annularCrossingTime r) = Real.sqrt (1 + r ^ 2) / r := by
  rw [Real.exp_neg, exp_annularCrossingTime hr, inv_div]

theorem annularCrossingTime_nonpos {r : ℝ} (hr : 0 < r) : annularCrossingTime r ≤ 0 := by
  have hs : 0 < Real.sqrt (1 + r ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hsq := Real.sq_sqrt (show 0 ≤ 1 + r ^ 2 by positivity)
  apply Real.log_nonpos (div_nonneg hr.le hs.le)
  apply (div_le_one hs).mpr
  nlinarith

variable {N P : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
  [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem norm_annularDirection {v : P} (hv : v ≠ 0) : ‖‖v‖⁻¹ • v‖ = 1 := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg v))]
  exact inv_mul_cancel₀ (norm_pos_iff.mpr hv).ne'

def annularUpperModel (ρ : ℝ) (u : N) (v : P) : N × P :=
  beltLevelModel ρ (‖v‖ • u) (‖v‖⁻¹ • v)

theorem annularUpperModel_height {ρ : ℝ} (hρ : 0 < ρ) (u : N) {v : P} (hv : v ≠ 0) :
    quadratic (annularUpperModel ρ u v) = ρ ^ 2 :=
  beltLevelModel_height hρ (‖v‖ • u) (norm_annularDirection hv)

theorem descentFlow_annularCrossingTime (ρ : ℝ) {u : N} (hu : ‖u‖ = 1)
    {v : P} (hv : v ≠ 0) :
    descentFlow (annularCrossingTime ‖v‖) (ambientMap ρ (u, v)) =
      annularUpperModel ρ u v := by
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hs : Real.sqrt (1 + ‖v‖ ^ 2) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  have hn : ‖‖v‖ • u‖ = ‖v‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg v), hu, mul_one]
  apply Prod.ext
  · change Real.exp (annularCrossingTime ‖v‖) •
        ((ρ * Real.sqrt (1 + ‖v‖ ^ 2)) • u) = ρ • (‖v‖ • u)
    rw [exp_annularCrossingTime hvpos, smul_smul, smul_smul]
    congr 1
    field_simp
  · change Real.exp (-annularCrossingTime ‖v‖) • (ρ • v) =
      (ρ * Real.sqrt (1 + ‖‖v‖ • u‖ ^ 2)) • (‖v‖⁻¹ • v)
    rw [hn, exp_neg_annularCrossingTime hvpos, smul_smul, smul_smul]
    congr 1
    field_simp

theorem descentFlow_annular_mem_block {ρ : ℝ} (hρ : 0 < ρ) {u : N} (hu : ‖u‖ = 1)
    {v : P} (hv : v ≠ 0) (hvr : ‖v‖ ≤ (3 / 2 : ℝ)) {t : ℝ}
    (ht : t ∈ uIcc 0 (annularCrossingTime ‖v‖)) :
    descentFlow t (ambientMap ρ (u, v)) ∈
      closedBall (0 : N) (2 * ρ) ×ˢ closedBall (0 : P) (2 * ρ) := by
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hspos : 0 < Real.sqrt (1 + ‖v‖ ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hs : Real.sqrt (1 + ‖v‖ ^ 2) ≤ 2 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, by nlinarith [norm_nonneg v]⟩
  rw [uIcc_of_ge (annularCrossingTime_nonpos hvpos)] at ht
  have he : Real.exp t ≤ 1 := Real.exp_le_one_iff.mpr ht.2
  have hen : Real.exp (-t) ≤ Real.sqrt (1 + ‖v‖ ^ 2) / ‖v‖ := by
    rw [← exp_neg_annularCrossingTime hvpos]
    exact Real.exp_le_exp.mpr (neg_le_neg ht.1)
  constructor
  · rw [mem_closedBall_zero_iff, norm_descentFlow_fst]
    change Real.exp t * ‖(ρ * Real.sqrt (1 + ‖v‖ ^ 2)) • u‖ ≤ 2 * ρ
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (mul_pos hρ hspos), hu, mul_one]
    calc
      _ ≤ ρ * Real.sqrt (1 + ‖v‖ ^ 2) := mul_le_of_le_one_left (mul_pos hρ hspos).le he
      _ ≤ 2 * ρ := by nlinarith
  · rw [mem_closedBall_zero_iff, norm_descentFlow_snd]
    change Real.exp (-t) * ‖ρ • v‖ ≤ 2 * ρ
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hρ]
    calc
      _ ≤ (Real.sqrt (1 + ‖v‖ ^ 2) / ‖v‖) * (ρ * ‖v‖) :=
        mul_le_mul_of_nonneg_right hen (mul_pos hρ hvpos).le
      _ = ρ * Real.sqrt (1 + ‖v‖ ^ 2) := by field_simp
      _ ≤ 2 * ρ := by nlinarith

end Wikipedia.SmoothSixDPoincare.MorseHandle
