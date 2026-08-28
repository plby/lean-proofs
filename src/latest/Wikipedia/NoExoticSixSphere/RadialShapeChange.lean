import Wikipedia.NoExoticSixSphere.QuadraticRadialCompression
import Mathlib.Analysis.Normed.Operator.Basic

/-! # Exact conversion from an ellipsoidal radial tube to a smaller round tube -/

noncomputable section

namespace NoExoticSixSphere.RadialShapeChange

variable {K : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K]
  (L : K →L[ℝ] K) (s : ℝ)

def defect (v : K) : ℝ := ‖v‖ ^ 2 - s ^ 2 * ‖L v‖ ^ 2

theorem defect_nonneg (hs : 0 ≤ s) (hb : ∀ v, s * ‖L v‖ ≤ ‖v‖) (v : K) :
    0 ≤ defect L s v := by
  have h := (sq_le_sq₀ (mul_nonneg hs (norm_nonneg (L v))) (norm_nonneg v)).mpr (hb v)
  change 0 ≤ ‖v‖ ^ 2 - s ^ 2 * ‖L v‖ ^ 2
  nlinarith

theorem defect_smul (c : ℝ) (v : K) : defect L s (c • v) = c ^ 2 * defect L s v := by
  simp only [defect, map_smul, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

theorem continuous_defect : Continuous (defect L s) :=
  (continuous_norm.pow 2).sub (continuous_const.mul (L.continuous.norm.pow 2))

def finalCoordinates (v : K) : K := s • L ((Real.sqrt (1 + defect L s v))⁻¹ • v)

theorem norm_finalCoordinates_sq (hs : 0 ≤ s) (hb : ∀ v, s * ‖L v‖ ≤ ‖v‖) (v : K) :
    ‖finalCoordinates L s v‖ ^ 2 = s ^ 2 * ‖L v‖ ^ 2 / (1 + defect L s v) := by
  rw [finalCoordinates, map_smul, norm_smul, norm_smul]
  simp only [Real.norm_eq_abs, mul_pow, sq_abs, inv_pow]
  rw [Real.sq_sqrt (by linarith [defect_nonneg L s hs hb v])]
  ring

theorem sqrt_finalCoordinates (hs : 0 ≤ s) (hb : ∀ v, s * ‖L v‖ ≤ ‖v‖) (v : K) :
    Real.sqrt (1 + ‖finalCoordinates L s v‖ ^ 2) =
      Real.sqrt (1 + ‖v‖ ^ 2) / Real.sqrt (1 + defect L s v) := by
  rw [norm_finalCoordinates_sq L s hs hb]
  rw [← Real.sqrt_div (by positivity)]
  congr 1
  have hd : 1 + defect L s v ≠ 0 := ne_of_gt (by linarith [defect_nonneg L s hs hb v])
  field_simp
  simp only [defect]
  ring

theorem univBall_finalCoordinates (hs : 0 < s) (hb : ∀ v, s * ‖L v‖ ≤ ‖v‖)
    (r : ℝ) (hr : 0 < r) (v : K) :
    OpenPartialHomeomorph.univBall (0 : K) r (finalCoordinates L s v) =
      L (OpenPartialHomeomorph.univBall (0 : K) (r * s) v) := by
  rw [OpenPartialHomeomorph.univBall, dif_pos hr,
    OpenPartialHomeomorph.univBall, dif_pos (mul_pos hr hs)]
  change r • ((Real.sqrt (1 + ‖finalCoordinates L s v‖ ^ 2))⁻¹ •
    finalCoordinates L s v) + 0 = L ((r * s) • ((Real.sqrt (1 + ‖v‖ ^ 2))⁻¹ • v) + 0)
  rw [sqrt_finalCoordinates L s hs.le hb, finalCoordinates]
  simp only [map_smul, add_zero, smul_smul]
  have hd : Real.sqrt (1 + defect L s v) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr (by linarith [defect_nonneg L s hs.le hb v])
  congr 1
  field_simp

end NoExoticSixSphere.RadialShapeChange
