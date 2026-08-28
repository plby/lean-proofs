import Wikipedia.HopfProblem.DegreeCollapseRelativeBumpPreparation

/-!
# Construct all ambient transverse patches inside a prescribed open set

Only the actual compact chart support must lie in the open set. Choose
the cutoff in the inverse chart's open preimage, preserving the original
compact source core and target plateau needed by the finite induction.
-/

noncomputable section

open Set Function Filter Metric
open scoped ContDiff Manifold Topology
open Wikipedia.SmoothSixDPoincare NativeTransversality
open Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationTransport

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseRearrangement

variable {G K N X : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace K] {J : ModelWithCorners ℝ G K}
  [TopologicalSpace N] [ChartedSpace K N]
  [TopologicalSpace X]

theorem ambient_patch_support_compact (p : Patch J X (N := N)) :
    IsCompact (p.chart.symm '' tsupport p.cutoff) :=
  p.cutoff_compact.isCompact.image_of_continuousOn
    (p.chart.contMDiffOn_invFun.continuousOn.mono p.cutoff_support)

variable [FiniteDimensional ℝ G] [J.Boundaryless] [IsManifold J ∞ N]
  [CompactSpace X] [T2Space X]

theorem exists_ambient_patch_in_open {f : X → N} (hf : Continuous f)
    {U : Set N} (hU : IsOpen U) (x : X) (hfxU : f x ∈ U) :
    ∃ p : Patch J X (N := N), p.Compatible f ∧ x ∈ interior p.core ∧
      p.chart.symm '' tsupport p.cutoff ⊆ U := by
  let c := NoExoticSixSphere.modelChartPartialDiffeomorph (I := J) (f x)
  have hcx : f x ∈ c.source := mem_extChartAt_source _
  let V : Set G := c.target ∩ c.symm ⁻¹' U
  have hV : IsOpen V :=
    c.contMDiffOn_invFun.continuousOn.isOpen_inter_preimage c.open_target hU
  have hcv : c (f x) ∈ V := ⟨c.map_source' hcx, by
    change c.symm (c (f x)) ∈ U
    have heq : c.symm (c (f x)) = f x := c.left_inv' hcx
    rw [heq]
    exact hfxU⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hcv)
  obtain ⟨β, hβ, hsupport, W, hW, hcenter, -, hone⟩ :=
    exists_smooth_cutoff_near_closed
      (K := {c (f x)}) (U := ball (c (f x)) r) isClosed_singleton isOpen_ball
      (singleton_subset_iff.mpr (mem_ball_self hr))
  have hcompact : HasCompactSupport β :=
    (isCompact_closedBall (c (f x)) r).of_isClosed_subset (isClosed_tsupport β)
      (hsupport.trans ball_subset_closedBall)
  let O : Set N := c.source ∩ c ⁻¹' W
  have hO : IsOpen O := c.contMDiffOn_toFun.continuousOn.isOpen_inter_preimage c.open_source hW
  have hfx : f x ∈ O := ⟨hcx, hcenter (mem_singleton _)⟩
  obtain ⟨C, hC, -, hxC, hCO⟩ := exists_compact_closed_between
    (isCompact_singleton (x := x)) (hO.preimage hf) (singleton_subset_iff.mpr hfx)
  let p : Patch J X (N := N) := {
    core := C
    core_compact := hC
    chart := c
    cutoff := β
    cutoff_smooth := hβ
    cutoff_compact := hcompact
    cutoff_support := hsupport.trans (hball.trans inter_subset_left)
    plateau := O
    plateau_open := hO
    plateau_source := inter_subset_left
    plateau_one := by
      intro y hy
      filter_upwards [hW.mem_nhds hy.2] with z hz
      exact hone hz }
  refine ⟨p, hCO, hxC (mem_singleton x), ?_⟩
  rintro y ⟨z, hz, rfl⟩
  exact (hball (hsupport hz)).2

end Wikipedia.HopfProblem.DegreeCollapse.MorseRearrangement
