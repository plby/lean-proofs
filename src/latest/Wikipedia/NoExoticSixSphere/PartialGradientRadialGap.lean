import Wikipedia.NoExoticSixSphere.PartialGradientRadialEnergy

/-!
# A uniform energy gap at the radial endpoint

The negative-fiber Hessian bound gives a positive energy drop, independent of
the initial nonzero fiber displacement, once radial expansion reaches a fixed
positive radius. The estimate uses the operator norm of the negative-family
map and does not change the norm on the ambient model space.
-/

open Set unitInterval
open scoped Topology ContDiff

namespace NoExoticSixSphere.PartialGradientCoordinates.LocalData

variable {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f : E → ℝ} {L : D →L[ℝ] E} {U : Set E} (C : LocalData f L U)

theorem exists_fiber_boundary_gap (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (r : ℝ) (hr : 0 < r) (hball : Metric.ball (0 : E) (3 * r) ⊆ C.chart.source) :
    ∃ δ > 0, ∀ z ∈ C.radialDomain r, ‖z - C.center z‖ = r →
      f z ≤ f (C.center z) - δ := by
  obtain ⟨c, hc, henergy⟩ := C.exists_fiber_energy_bound hU hf
  have hden : 0 < ‖L‖ + 1 := by positivity
  let δ := (c / 2) * (r / (‖L‖ + 1)) ^ 2
  have hδ : 0 < δ := mul_pos (by linarith) (sq_pos_of_pos (div_pos hr hden))
  refine ⟨δ, hδ, fun z hz hRadius ↦ ?_⟩
  obtain ⟨w, hw⟩ := C.center_same_fiber hz.1
  have hd : z - C.center z = L w := by
    simpa only [add_sub_cancel_left] using congrArg (fun x : E ↦ x - C.center z) hw
  have hwNorm : r ≤ (‖L‖ + 1) * ‖w‖ := by
    rw [hd] at hRadius
    have hL := L.le_opNorm w
    nlinarith [norm_nonneg w]
  have hlower : r / (‖L‖ + 1) ≤ ‖w‖ := (div_le_iff₀ hden).mpr (by nlinarith [hwNorm])
  have hsq : (r / (‖L‖ + 1)) ^ 2 ≤ ‖w‖ ^ 2 :=
    pow_le_pow_left₀ (le_of_lt (div_pos hr hden)) hlower 2
  have hdrop : δ ≤ (c / 2) * ‖w‖ ^ 2 :=
    mul_le_mul_of_nonneg_left hsq (by linarith)
  have hb := (henergy (C.center z) (C.gradient_center hz.1) w 1 zero_le_one
    (fun t ht ↦ C.ray_mem_source r hr hball hz hw (by
      rw [hRadius, div_self hr.ne']
      exact ht))).1
  simp only [one_smul, one_pow, mul_one, ← hw] at hb
  linarith

theorem exists_radial_endpoint_gap (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (r : ℝ) (hr : 0 < r) (hball : Metric.ball (0 : E) (3 * r) ⊆ C.chart.source) :
    ∃ δ > 0, ∀ z ∈ C.radialDomain r,
      f (C.radial r (1, z)) ≤ f (C.center z) - δ := by
  obtain ⟨δ, hδ, hgap⟩ := C.exists_fiber_boundary_gap hU hf r hr hball
  refine ⟨δ, hδ, fun z hz ↦ ?_⟩
  have hnew := C.radial_mem_domain r hr hball hz (1 : I)
  have hRadius := C.radial_one_norm r hz
  have hg := hgap (C.radial r (1, z)) hnew hRadius
  rwa [C.center_radial r hz (1 : I)] at hg

end NoExoticSixSphere.PartialGradientCoordinates.LocalData
