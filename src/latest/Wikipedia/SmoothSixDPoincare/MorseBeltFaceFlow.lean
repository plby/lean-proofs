import Wikipedia.SmoothSixDPoincare.MorseBeltFaceCoordinates
import Wikipedia.SmoothSixDPoincare.MorseModelFlow

/-!
# Exact flow between the upper Morse level and the positive handle face

The full trajectory, in either direction, stays in the controlled product
block. Thus the native model-orbit theorem applies to its endpoints.
-/

noncomputable section

open Set Metric

namespace Wikipedia.SmoothSixDPoincare.MorseHandle

/-- Descent time from the upper level to the positive handle face. -/
def beltFaceTime (r : ℝ) : ℝ := Real.log (Real.sqrt (1 + r ^ 2))

theorem beltFaceTime_nonneg (r : ℝ) : 0 ≤ beltFaceTime r :=
  Real.log_nonneg (Real.one_le_sqrt.mpr (by nlinarith [sq_nonneg r]))

theorem exp_beltFaceTime (r : ℝ) :
    Real.exp (beltFaceTime r) = Real.sqrt (1 + r ^ 2) :=
  Real.exp_log (Real.sqrt_pos.mpr (by positivity))

variable {N P : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
  [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- Raw upper-level coordinates with positive sphere direction `v`. -/
def beltLevelModel (ρ : ℝ) (u : N) (v : P) : N × P :=
  (ρ • u, (ρ * Real.sqrt (1 + ‖u‖ ^ 2)) • v)

theorem beltLevelModel_height {ρ : ℝ} (hρ : 0 < ρ) (u : N) {v : P} (hv : ‖v‖ = 1) :
    quadratic (beltLevelModel ρ u v) = ρ ^ 2 := by
  have hs : 0 < Real.sqrt (1 + ‖u‖ ^ 2) := Real.sqrt_pos.mpr (by positivity)
  simp only [quadratic, beltLevelModel, norm_smul, Real.norm_eq_abs,
    abs_of_pos hρ, abs_of_pos (mul_pos hρ hs), hv, mul_one, mul_pow,
    Real.sq_sqrt (show 0 ≤ 1 + ‖u‖ ^ 2 by positivity)]
  ring

/-- The endpoint is exactly the curved handle's positive face, with the radial
negative-coordinate change proved in `MorseBeltFaceCoordinates`. -/
theorem descentFlow_beltFaceTime (ρ : ℝ) (u : UnitDisk N) (v : UnitDisk P)
    (hv : ‖v.val‖ = 1) :
    descentFlow (beltFaceTime ‖u.val‖) (beltLevelModel ρ u.val v.val) =
      modelMap ρ (beltFaceDiskMap u, v) := by
  have hs : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hu : Real.sqrt (1 + ‖u.val‖ ^ 2) ≠ 0 :=
    (Real.sqrt_pos.mpr (by positivity)).ne'
  apply Prod.ext
  · change Real.exp (beltFaceTime ‖u.val‖) • (ρ • u.val) =
      (ρ * Real.sqrt (1 + ‖v.val‖ ^ 2)) • (beltFaceScale ‖u.val‖ • u.val)
    rw [exp_beltFaceTime, hv, one_pow, one_add_one_eq_two, smul_smul, smul_smul]
    congr 1
    unfold beltFaceScale
    field_simp
  · change Real.exp (-beltFaceTime ‖u.val‖) •
      ((ρ * Real.sqrt (1 + ‖u.val‖ ^ 2)) • v.val) = ρ • v.val
    rw [Real.exp_neg, exp_beltFaceTime, smul_smul]
    congr 1
    field_simp

/-- The whole forward model trajectory fits in the original controlled block. -/
theorem descentFlow_beltLevelModel_mem_block {ρ : ℝ} (hρ : 0 < ρ)
    (u : UnitDisk N) {v : P} (hv : ‖v‖ = 1) {t : ℝ}
    (ht : t ∈ Icc 0 (beltFaceTime ‖u.val‖)) :
    descentFlow t (beltLevelModel ρ u.val v) ∈
      closedBall (0 : N) (2 * ρ) ×ˢ closedBall (0 : P) (2 * ρ) := by
  have hu : ‖u.val‖ ≤ 1 := mem_closedBall_zero_iff.mp u.property
  have hspos : 0 < Real.sqrt (1 + ‖u.val‖ ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hs : Real.sqrt (1 + ‖u.val‖ ^ 2) ≤ 2 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, by nlinarith [norm_nonneg u.val]⟩
  have he : Real.exp t ≤ Real.sqrt (1 + ‖u.val‖ ^ 2) := by
    rw [← exp_beltFaceTime]
    exact Real.exp_le_exp.mpr ht.2
  have hen : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht.1)
  constructor
  · rw [mem_closedBall_zero_iff, norm_descentFlow_fst]
    change Real.exp t * ‖ρ • u.val‖ ≤ 2 * ρ
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hρ]
    calc
      _ ≤ Real.exp t * ρ := mul_le_mul_of_nonneg_left
        (mul_le_of_le_one_right hρ.le hu) (Real.exp_pos t).le
      _ ≤ 2 * ρ := mul_le_mul_of_nonneg_right (he.trans hs) hρ.le
  · rw [mem_closedBall_zero_iff, norm_descentFlow_snd]
    change Real.exp (-t) * ‖(ρ * Real.sqrt (1 + ‖u.val‖ ^ 2)) • v‖ ≤ 2 * ρ
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (mul_pos hρ hspos), hv, mul_one]
    calc
      _ ≤ ρ * Real.sqrt (1 + ‖u.val‖ ^ 2) :=
        mul_le_of_le_one_left (mul_pos hρ hspos).le hen
      _ ≤ ρ * 2 := mul_le_mul_of_nonneg_left hs hρ.le
      _ = 2 * ρ := mul_comm _ _

/-- The backward endpoint is the original upper-level coordinate point. -/
theorem descentFlow_neg_beltFaceTime (ρ : ℝ) (u : UnitDisk N) (v : UnitDisk P)
    (hv : ‖v.val‖ = 1) :
    descentFlow (-beltFaceTime ‖u.val‖) (modelMap ρ (beltFaceDiskMap u, v)) =
      beltLevelModel ρ u.val v.val := by
  rw [← descentFlow_beltFaceTime ρ u v hv, ← descentFlow.map_add,
    neg_add_cancel, descentFlow.map_zero_apply]

/-- The full backward trajectory, including both endpoints, stays in the block. -/
theorem descentFlow_positiveFace_mem_block {ρ : ℝ} (hρ : 0 < ρ)
    (u : UnitDisk N) (v : UnitDisk P) (hv : ‖v.val‖ = 1) {t : ℝ}
    (ht : t ∈ uIcc 0 (-beltFaceTime ‖u.val‖)) :
    descentFlow t (modelMap ρ (beltFaceDiskMap u, v)) ∈
      closedBall (0 : N) (2 * ρ) ×ˢ closedBall (0 : P) (2 * ρ) := by
  rw [uIcc_of_ge (neg_nonpos.mpr (beltFaceTime_nonneg ‖u.val‖))] at ht
  rw [← descentFlow_beltFaceTime ρ u v hv, ← descentFlow.map_add]
  apply descentFlow_beltLevelModel_mem_block hρ u hv
  constructor <;> linarith [ht.1, ht.2]

end Wikipedia.SmoothSixDPoincare.MorseHandle
