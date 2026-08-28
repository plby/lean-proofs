import Wikipedia.SmoothSixDPoincare.ControlledMorseBlock

/-!
# Morse extrema have no coordinate directions of the opposite sign

A local minimum forces the negative coordinate space to be zero, and a
local maximum forces the positive coordinate space to be zero. The proof
uses the actual normal-form chart in an extremum neighborhood.
-/

noncomputable section

open Set Metric Manifold Filter
open scoped ContDiff Topology

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.SignedMorseChart

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  {f : M → ℝ} {p : M} (c : SignedMorseChart (E := E) f p)

open Classical in
/-- At a local minimum every negative Morse coordinate is zero. -/
theorem negative_eq_zero_of_localMin (hmin : IsLocalMin f p) (u : c.NegativeCoordinates) :
    u = 0 := by
  by_contra hu
  have hnorm : 0 < ‖u‖ := norm_pos_iff.mpr hu
  obtain ⟨U, hUmin, hU, hpU⟩ := _root_.mem_nhds_iff.mp hmin
  obtain ⟨r, hr, hblock⟩ := c.exists_closed_productBlock_in hU hpU
  let z : c.NegativeCoordinates := (r / ‖u‖) • u
  have hz : ‖z‖ = r := by
    rw [show z = (r / ‖u‖) • u from rfl, norm_smul, Real.norm_eq_abs,
      abs_of_pos (div_pos hr hnorm), div_mul_cancel₀ _ hnorm.ne']
  have hpoint := hblock (show (z, (0 : c.PositiveCoordinates)) ∈
      closedBall 0 r ×ˢ closedBall 0 r from
    ⟨mem_closedBall_zero_iff.mpr hz.le, by
      simpa only [mem_closedBall_zero_iff, norm_zero] using hr.le⟩)
  have hh := hUmin hpoint.2
  change f p ≤ f (c.splitChart.symm (z, (0 : c.PositiveCoordinates))) at hh
  rw [c.splitChart_inverse_equation hpoint.1, hz, norm_zero] at hh
  nlinarith [sq_pos_of_pos hr]

open Classical in
theorem subsingleton_negative_of_localMin (hmin : IsLocalMin f p) :
    Subsingleton c.NegativeCoordinates :=
  ⟨fun u v => (c.negative_eq_zero_of_localMin hmin u).trans
    (c.negative_eq_zero_of_localMin hmin v).symm⟩

open Classical in
/-- At a local maximum every positive Morse coordinate is zero. -/
theorem positive_eq_zero_of_localMax (hmax : IsLocalMax f p) (v : c.PositiveCoordinates) :
    v = 0 := by
  by_contra hv
  have hnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
  obtain ⟨U, hUmax, hU, hpU⟩ := _root_.mem_nhds_iff.mp hmax
  obtain ⟨r, hr, hblock⟩ := c.exists_closed_productBlock_in hU hpU
  let z : c.PositiveCoordinates := (r / ‖v‖) • v
  have hz : ‖z‖ = r := by
    rw [show z = (r / ‖v‖) • v from rfl, norm_smul, Real.norm_eq_abs,
      abs_of_pos (div_pos hr hnorm), div_mul_cancel₀ _ hnorm.ne']
  have hpoint := hblock (show ((0 : c.NegativeCoordinates), z) ∈
      closedBall 0 r ×ˢ closedBall 0 r from
    ⟨by simpa only [mem_closedBall_zero_iff, norm_zero] using hr.le,
      mem_closedBall_zero_iff.mpr hz.le⟩)
  have hh := hUmax hpoint.2
  change f (c.splitChart.symm ((0 : c.NegativeCoordinates), z)) ≤ f p at hh
  rw [c.splitChart_inverse_equation hpoint.1, norm_zero, hz] at hh
  nlinarith [sq_pos_of_pos hr]

open Classical in
theorem subsingleton_positive_of_localMax (hmax : IsLocalMax f p) :
    Subsingleton c.PositiveCoordinates :=
  ⟨fun u v => (c.positive_eq_zero_of_localMax hmax u).trans
    (c.positive_eq_zero_of_localMax hmax v).symm⟩

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.SignedMorseChart
