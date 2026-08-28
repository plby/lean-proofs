import Wikipedia.SmoothSixDPoincare.TubularSheetTransition
import Wikipedia.SmoothSixDPoincare.TwoSheetTubularBigon
import Wikipedia.SmoothSixDPoincare.BigonArcDerivatives

/-!
# The first columns of the actual sheet transitions along the whole bigon boundary

Full preserved strip germs, not merely equality on the closed interval,
identify the tubular-coordinate boundary curves. This proves the true
two-sided derivative formulas at both corners as well as in the arc interiors.
-/

noncomputable section

open Set Function Filter Topology
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.TubularBigon

open WhitneyPairModel

variable {E M A B : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B]
  {S T : Set M} {a b : ℝ → M} {k l : (ℝ × ℝ) → M} {h : ℝ} {n : ℕ}
  (tube : TubularBigon (E := E) S T a b k l h n)

include tube in
theorem lowerBoundaryArc_mem_bigon {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    lowerBoundaryArc t ∈ bigon h := by
  have hf : lowerBoundaryArc t ∈ frontier (bigon h) :=
    (mem_frontier_bigon_iff_exists_time tube.height_pos _).mpr ⟨t, ht, Or.inl rfl⟩
  exact ((mem_frontier_bigon_iff h _).mp hf).1

include tube in
theorem upperBoundaryArc_mem_bigon {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    upperBoundaryArc h t ∈ bigon h := by
  have hf : upperBoundaryArc h t ∈ frontier (bigon h) :=
    (mem_frontier_bigon_iff_exists_time tube.height_pos _).mpr ⟨t, ht, Or.inr rfl⟩
  exact ((mem_frontier_bigon_iff h _).mp hf).1

theorem lowerBoundaryArc_zero_mem_source {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (lowerBoundaryArc t, 0) ∈ tube.chart.source :=
  tube.source_contains ⟨tube.lowerBoundaryArc_mem_bigon ht,
    Metric.mem_closedBall_self tube.radius_pos.le⟩

theorem upperBoundaryArc_zero_mem_source {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (upperBoundaryArc h t, 0) ∈ tube.chart.source :=
  tube.source_contains ⟨tube.upperBoundaryArc_mem_bigon ht,
    Metric.mem_closedBall_self tube.radius_pos.le⟩

theorem lower_chart_center_mem_target (d : StripNormalData A B (E := E) S k)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    d.chart (StripCoordinates.center t) ∈ tube.chart.target := by
  have hg := (tube.lower_germ t ht).eq_of_nhds
  dsimp only [Function.comp_apply] at hg
  rw [lowerStripCoordinates_lower, d.center t] at hg
  have hp := tube.chart.map_source' (tube.lowerBoundaryArc_zero_mem_source ht)
  rw [tube.zero_section, lowerBoundaryArc, hg] at hp
  exact hp

theorem upper_chart_center_mem_target (d : StripNormalData A B (E := E) T l)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    d.chart (StripCoordinates.center t) ∈ tube.chart.target := by
  have hg := (tube.upper_germ t ht).eq_of_nhds
  dsimp only [Function.comp_apply] at hg
  rw [upperStripCoordinates_upper, d.center t] at hg
  have hp := tube.chart.map_source' (tube.upperBoundaryArc_zero_mem_source ht)
  rw [tube.zero_section, upperBoundaryArc, hg] at hp
  exact hp

theorem lower_sheetTransition_center_germ (d : StripNormalData A B (E := E) S k)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (fun s : ℝ => d.sheetTransition tube.chart (s, 0)) =ᶠ[𝓝 t]
      fun s => (lowerBoundaryArc s, 0) :=
  d.sheetTransition_center_germ tube.chart tube.zero_section
    (hasDerivAt_lowerBoundaryArc t).continuousAt (tube.lowerBoundaryArc_zero_mem_source ht)
    (lowerStripCoordinates_lower h) (tube.lower_germ t ht)

theorem upper_sheetTransition_center_germ (d : StripNormalData A B (E := E) T l)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (fun s : ℝ => d.sheetTransition tube.chart (s, 0)) =ᶠ[𝓝 t]
      fun s => (upperBoundaryArc h s, 0) :=
  d.sheetTransition_center_germ tube.chart tube.zero_section
    (hasDerivAt_upperBoundaryArc h t).continuousAt (tube.upperBoundaryArc_zero_mem_source ht)
    (upperStripCoordinates_upper h) (tube.upper_germ t ht)

/-- The first lower sheet column is exactly the lower disk-boundary tangent, even at the corners. -/
theorem lower_sheetDifferential_arc (d : StripNormalData A B (E := E) S k)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    d.sheetDifferential tube.chart t (1, 0) = ((2, 0), 0) :=
  d.sheetDifferential_arc_of_germ tube.chart ht (tube.lower_chart_center_mem_target d ht)
    (hasDerivAt_lowerBoundaryArc t) (tube.lower_sheetTransition_center_germ d ht)

/-- The first upper sheet column is exactly the upper disk-boundary tangent, including corners. -/
theorem upper_sheetDifferential_arc (d : StripNormalData A B (E := E) T l)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    d.sheetDifferential tube.chart t (1, 0) = ((2, -4 * h * (2 * t - 1)), 0) :=
  d.sheetDifferential_arc_of_germ tube.chart ht (tube.upper_chart_center_mem_target d ht)
    (hasDerivAt_upperBoundaryArc h t) (tube.upper_sheetTransition_center_germ d ht)

end Wikipedia.SmoothSixDPoincare.TubularBigon
