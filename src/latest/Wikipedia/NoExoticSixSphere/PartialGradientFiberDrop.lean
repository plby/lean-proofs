import Wikipedia.NoExoticSixSphere.PartialGradientFiberEnergy
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp

/-!
# Quantitative energy loss between two points of a negative ray

The second-derivative estimate compares any two ordered points on the ray,
not just the center and endpoint. It bounds the loss by the difference of
their squared ray parameters, uniformly over the verified local data.
-/

open Set
open scoped ContDiff

namespace NoExoticSixSphere.PartialGradientCoordinates.LocalData

variable {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f : E → ℝ} {L : D →L[ℝ] E} {U : Set E} (C : LocalData f L U)

theorem exists_fiber_secant_bound (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) :
    ∃ c > 0, ∀ p : E, gradient f L p = 0 → ∀ (w : D) (T : ℝ), 0 ≤ T →
      (∀ t ∈ Icc (0 : ℝ) T, p + t • L w ∈ C.chart.source) →
      ∀ s t : ℝ, s ∈ Icc (0 : ℝ) T → t ∈ Icc (0 : ℝ) T → s ≤ t →
        f (p + t • L w) ≤ f (p + s • L w) - (c / 2) * (t ^ 2 - s ^ 2) * ‖w‖ ^ 2 := by
  obtain ⟨c, hc, hbound⟩ := C.uniform_bound
  have hf2 : ContDiffOn ℝ 2 f U := hf.of_le (WithTop.coe_le_coe.mpr le_top)
  refine ⟨c, hc, ?_⟩
  intro p hp w T hT hseg s t hs ht hst
  have hz : fderiv ℝ f p (L w) = 0 := by
    have hh := congrArg (fun ℓ : D →L[ℝ] ℝ ↦ ℓ w) hp
    simpa only [gradient_apply, zero_apply] using hh
  have hb : ∀ t ∈ Icc (0 : ℝ) T,
      fderiv ℝ (fderiv ℝ f) (p + t • L w) (L w) (L w) ≤ -(c * ‖w‖ ^ 2) := by
    intro t ht
    simpa only [neg_mul] using hbound _ (hseg t ht) w
  have hh := AffineLineSecondDerivative.quadratic_secant_upper f p (L w) U hU hf2
    (c * ‖w‖ ^ 2) T hT (fun t ht ↦ C.source_subset (hseg t ht)) hb hs ht hst
  rw [hz, zero_mul, add_zero] at hh
  convert! hh using 1
  ring

theorem exists_fiber_displacement_bound (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) :
    ∃ c > 0, ∀ p : E, gradient f L p = 0 → ∀ (w : D) (T : ℝ), 0 ≤ T →
      (∀ t ∈ Icc (0 : ℝ) T, p + t • L w ∈ C.chart.source) →
      ∀ s t : ℝ, s ∈ Icc (0 : ℝ) T → t ∈ Icc (0 : ℝ) T → s ≤ t →
        c * dist (p + t • L w) (p + s • L w) ^ 2 ≤
          f (p + s • L w) - f (p + t • L w) := by
  obtain ⟨a, ha, hsec⟩ := C.exists_fiber_secant_bound hU hf
  have hden : 0 < ‖L‖ + 1 := by positivity
  let c := (a / 2) / (‖L‖ + 1) ^ 2
  have hc : 0 < c := div_pos (by linarith) (sq_pos_of_pos hden)
  refine ⟨c, hc, ?_⟩
  intro p hp w T hT hseg s t hs ht hst
  have henergy := hsec p hp w T hT hseg s t hs ht hst
  have hparam : (t - s) ^ 2 ≤ t ^ 2 - s ^ 2 := by
    nlinarith [mul_nonneg hs.1 (sub_nonneg.mpr hst)]
  have hdrop := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hparam (by linarith : 0 ≤ a / 2)) (sq_nonneg ‖w‖)
  have hv : ‖(t - s) • w‖ ^ 2 = (t - s) ^ 2 * ‖w‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hst), mul_pow]
  have hd : (p + t • L w) - (p + s • L w) = L ((t - s) • w) := by
    rw [map_smul, sub_smul]
    abel
  have hnorm : dist (p + t • L w) (p + s • L w) ≤ (‖L‖ + 1) * ‖(t - s) • w‖ := by
    rw [dist_eq_norm, hd]
    have hh := L.le_opNorm ((t - s) • w)
    nlinarith [norm_nonneg ((t - s) • w)]
  have hnorm2 := pow_le_pow_left₀ (dist_nonneg : 0 ≤ dist (p + t • L w) (p + s • L w))
    hnorm 2
  calc
    c * dist (p + t • L w) (p + s • L w) ^ 2 ≤
        c * ((‖L‖ + 1) * ‖(t - s) • w‖) ^ 2 :=
      mul_le_mul_of_nonneg_left hnorm2 hc.le
    _ = (a / 2) * ‖(t - s) • w‖ ^ 2 := by
      dsimp [c]
      field_simp [hden.ne']
    _ ≤ (a / 2) * (t ^ 2 - s ^ 2) * ‖w‖ ^ 2 := by
      rw [hv]
      simpa only [mul_assoc] using hdrop
    _ ≤ f (p + s • L w) - f (p + t • L w) := by linarith

end NoExoticSixSphere.PartialGradientCoordinates.LocalData
