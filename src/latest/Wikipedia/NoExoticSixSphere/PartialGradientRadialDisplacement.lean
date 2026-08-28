import Wikipedia.NoExoticSixSphere.PartialGradientFiberDrop
import Wikipedia.NoExoticSixSphere.PartialGradientRadialEnergy

/-!
# Radial movement is controlled by energy loss

A single positive constant bounds squared ambient displacement by the energy
lost under every valid local radial expansion. The constant is independent of
the radial radius. Thus a point that loses little energy can move only a little.
-/

open Set unitInterval
open scoped Topology ContDiff

namespace NoExoticSixSphere.PartialGradientCoordinates.LocalData

variable {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f : E → ℝ} {L : D →L[ℝ] E} {U : Set E} (C : LocalData f L U)

theorem exists_radial_displacement_bound (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) :
    ∃ c > 0, ∀ (r : ℝ), 0 < r → Metric.ball (0 : E) (3 * r) ⊆ C.chart.source →
      ∀ z ∈ C.radialDomain r, ∀ s : I,
        c * dist (C.radial r (s, z)) z ^ 2 ≤ f z - f (C.radial r (s, z)) := by
  obtain ⟨c, hc, hbound⟩ := C.exists_fiber_displacement_bound hU hf
  refine ⟨c, hc, ?_⟩
  intro r hr hball z hz s
  obtain ⟨w, hw⟩ := C.center_same_fiber hz.1
  have hd : z - C.center z = L w := by
    simpa only [add_sub_cancel_left] using congrArg (fun x : E ↦ x - C.center z) hw
  have hn : 0 < ‖z - C.center z‖ := norm_pos_iff.mpr hz.2.2.1
  have hT : 1 ≤ r / ‖z - C.center z‖ := (le_div_iff₀ hn).mpr (by simpa using hz.2.2.2)
  have hs := RadialExpansion.scale_bounds r hz.2.2.1 hz.2.2.2 s
  have hh := hbound (C.center z) (C.gradient_center hz.1) w
    (r / ‖z - C.center z‖) (zero_le_one.trans hT)
    (fun _ ht ↦ C.ray_mem_source r hr hball hz hw ht)
    1 (RadialExpansion.scale r (s, z - C.center z)) ⟨zero_le_one, hT⟩
    ⟨zero_le_one.trans hs.1, hs.2⟩ hs.1
  have hrad : C.radial r (s, z) = C.center z +
      RadialExpansion.scale r (s, z - C.center z) • L w := by
    change C.center z + RadialExpansion.scale r (s, z - C.center z) •
      (z - C.center z) = _
    rw [hd]
  simpa only [one_smul, ← hw, ← hrad] using hh

theorem exists_radial_small_of_small_energy_loss (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ δ > 0, ∀ (r : ℝ), 0 < r → Metric.ball (0 : E) (3 * r) ⊆ C.chart.source →
      ∀ z ∈ C.radialDomain r, ∀ s : I,
        f z - f (C.radial r (s, z)) < δ → dist (C.radial r (s, z)) z < ρ := by
  obtain ⟨c, hc, hbound⟩ := C.exists_radial_displacement_bound hU hf
  refine ⟨c * ρ ^ 2, mul_pos hc (sq_pos_of_pos hρ), ?_⟩
  intro r hr hball z hz s hsmall
  have hh := hbound r hr hball z hz s
  by_contra hn
  have hlarge : ρ ≤ dist (C.radial r (s, z)) z := le_of_not_gt hn
  have hsquare := pow_le_pow_left₀ hρ.le hlarge 2
  have hcost := mul_le_mul_of_nonneg_left hsquare hc.le
  linarith

end NoExoticSixSphere.PartialGradientCoordinates.LocalData
