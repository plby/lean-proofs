import Wikipedia.NoExoticSixSphere.PartialGradientLocalData
import Wikipedia.NoExoticSixSphere.AffineLineSecondDerivative

/-!
# Quantitative energy decrease along the negative coordinate fibers

Starting at a point where the restricted differential vanishes, movement
along a negative affine fiber decreases energy quadratically. Along any
nonzero such ray, energy is strictly decreasing for nonnegative time, as
long as the segment remains in the verified coordinate source.
-/

open Set
open scoped ContDiff

namespace NoExoticSixSphere.PartialGradientCoordinates

variable {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem LocalData.exists_fiber_energy_bound {f : E → ℝ} {L : D →L[ℝ] E} {U : Set E}
    (C : LocalData f L U) (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) :
    ∃ c > 0, ∀ p : E, gradient f L p = 0 → ∀ (w : D) (T : ℝ), 0 ≤ T →
      (∀ t ∈ Icc (0 : ℝ) T, p + t • L w ∈ C.chart.source) →
      f (p + T • L w) ≤ f p - (c / 2) * T ^ 2 * ‖w‖ ^ 2 ∧
        (w ≠ 0 → StrictAntiOn (fun t : ℝ ↦ f (p + t • L w)) (Icc (0 : ℝ) T)) := by
  obtain ⟨c, hc, hbound⟩ := C.uniform_bound
  have hf2 : ContDiffOn ℝ 2 f U := hf.of_le (WithTop.coe_le_coe.mpr le_top)
  refine ⟨c, hc, ?_⟩
  intro p hp w T hT hseg
  have hz : fderiv ℝ f p (L w) = 0 := by
    have hh := congrArg (fun ℓ : D →L[ℝ] ℝ ↦ ℓ w) hp
    simpa only [gradient_apply, zero_apply] using hh
  have hs : ∀ t ∈ Icc (0 : ℝ) T, p + t • L w ∈ U :=
    fun t ht ↦ C.source_subset (hseg t ht)
  have hb : ∀ t ∈ Icc (0 : ℝ) T,
      fderiv ℝ (fderiv ℝ f) (p + t • L w) (L w) (L w) ≤ -(c * ‖w‖ ^ 2) := by
    intro t ht
    simpa only [neg_mul] using hbound _ (hseg t ht) w
  constructor
  · have hh := AffineLineSecondDerivative.quadratic_upper f p (L w) U hU hf2
      (c * ‖w‖ ^ 2) T hT hs hb
    rw [hz, zero_mul, add_zero] at hh
    convert! hh using 1
    ring
  · intro hw
    exact AffineLineSecondDerivative.strictAntiOn f p (L w) U hU hf2
      (c * ‖w‖ ^ 2) T hT (mul_pos hc (sq_pos_of_pos (norm_pos_iff.mpr hw))) hs hb hz

end NoExoticSixSphere.PartialGradientCoordinates
