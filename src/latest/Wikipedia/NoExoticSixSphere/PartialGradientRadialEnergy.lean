import Wikipedia.NoExoticSixSphere.PartialGradientRadial
import Wikipedia.NoExoticSixSphere.PartialGradientFiberEnergy

/-!
# The local radial homotopy never increases energy

Every radial homotopy slice moves outward along a negative affine ray from
its partial-critical center. The verified raywise energy monotonicity applies
because the entire relevant segment remains in the chart source.
-/

open Set unitInterval
open scoped Topology ContDiff

namespace NoExoticSixSphere.PartialGradientCoordinates.LocalData

variable {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f : E → ℝ} {L : D →L[ℝ] E} {U : Set E} (C : LocalData f L U)

theorem exists_radial_radius : ∃ r > 0, Metric.ball (0 : E) (3 * r) ⊆ C.chart.source := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp
    (C.chart.open_source.mem_nhds C.zero_mem_source)
  refine ⟨ε / 4, by linarith, ?_⟩
  exact (Metric.ball_subset_ball (by linarith)).trans hball

theorem ray_mem_source (r : ℝ) (hr : 0 < r)
    (hball : Metric.ball (0 : E) (3 * r) ⊆ C.chart.source)
    {z : E} (hz : z ∈ C.radialDomain r) {w : D} (hw : z = C.center z + L w)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (r / ‖z - C.center z‖)) :
    C.center z + t • L w ∈ C.chart.source := by
  have hd : z - C.center z = L w := by
    simpa only [add_sub_cancel_left] using congrArg (fun x : E ↦ x - C.center z) hw
  have hn : 0 < ‖z - C.center z‖ := norm_pos_iff.mpr hz.2.2.1
  have htbound : t * ‖z - C.center z‖ ≤ r := (le_div_iff₀ hn).mp ht.2
  have hnorm : ‖t • L w‖ = t * ‖z - C.center z‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1, ← hd]
  have hh := norm_add_le (C.center z) (t • L w)
  apply hball
  rw [Metric.mem_ball, dist_zero_right]
  rw [hnorm] at hh
  linarith [hz.2.1]

theorem energy_radial_le (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (r : ℝ) (hr : 0 < r) (hball : Metric.ball (0 : E) (3 * r) ⊆ C.chart.source)
    {z : E} (hz : z ∈ C.radialDomain r) (s : I) : f (C.radial r (s, z)) ≤ f z := by
  obtain ⟨w, hw⟩ := C.center_same_fiber hz.1
  have hd : z - C.center z = L w := by
    simpa only [add_sub_cancel_left] using congrArg (fun x : E ↦ x - C.center z) hw
  have hwne : w ≠ 0 := by
    intro h
    apply hz.2.2.1
    simpa only [h, _root_.map_zero] using hd
  have hn : 0 < ‖z - C.center z‖ := norm_pos_iff.mpr hz.2.2.1
  have hT : 1 ≤ r / ‖z - C.center z‖ := (le_div_iff₀ hn).mpr (by simpa using hz.2.2.2)
  obtain ⟨c, hc, henergy⟩ := C.exists_fiber_energy_bound hU hf
  have ha := (henergy (C.center z) (C.gradient_center hz.1) w
    (r / ‖z - C.center z‖) (zero_le_one.trans hT)
    (fun _ ht ↦ C.ray_mem_source r hr hball hz hw ht)).2 hwne
  have hs := RadialExpansion.scale_bounds r hz.2.2.1 hz.2.2.2 s
  have he := ha.antitoneOn ⟨zero_le_one, hT⟩ ⟨zero_le_one.trans hs.1, hs.2⟩ hs.1
  have hrad : C.radial r (s, z) = C.center z +
      RadialExpansion.scale r (s, z - C.center z) • L w := by
    change C.center z + RadialExpansion.scale r (s, z - C.center z) •
      (z - C.center z) = _
    rw [hd]
  rw [hrad]
  simpa only [one_smul, ← hw] using he

theorem radialHomotopy_energy_le (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (r : ℝ) (hr : 0 < r) (hball : Metric.ball (0 : E) (3 * r) ⊆ C.chart.source)
    (s : I) (z : C.radialDomain r) :
    f (C.radialHomotopy r hr hball (s, z)).1 ≤ f z.1 :=
  C.energy_radial_le hU hf r hr hball z.2 s

end NoExoticSixSphere.PartialGradientCoordinates.LocalData
