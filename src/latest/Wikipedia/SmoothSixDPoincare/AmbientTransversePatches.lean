import Wikipedia.SmoothSixDPoincare.AmbientTransversePlateau
import Wikipedia.SmoothSixDPoincare.NativeTransversalityStability
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationTransportCutoff

/-!
# Compact source cores and actual ambient transverse patches

Each patch has a compact source core, an open target plateau, and a genuine
smooth compactly supported coordinate cutoff. Compatibility is the actual
image containment of the core in the plateau. Such patches are constructed
around every point of a compact Hausdorff source.
-/

noncomputable section

open Set Function Filter Metric
open Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationTransport
open scoped ContDiff Manifold Topology

namespace Wikipedia.SmoothSixDPoincare.NativeTransversality

variable {G K N : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace K] (J : ModelWithCorners ℝ G K)
  [TopologicalSpace N] [ChartedSpace K N]

/-- All data for one actual compact-core ambient perturbation. -/
structure Patch (X : Type*) [TopologicalSpace X] where
  core : Set X
  core_compact : IsCompact core
  chart : PartialDiffeomorph J 𝓘(ℝ, G) N G ∞
  cutoff : G → ℝ
  cutoff_smooth : ContDiff ℝ ∞ cutoff
  cutoff_compact : HasCompactSupport cutoff
  cutoff_support : tsupport cutoff ⊆ chart.target
  plateau : Set N
  plateau_open : IsOpen plateau
  plateau_source : plateau ⊆ chart.source
  plateau_one : ∀ y ∈ plateau, cutoff =ᶠ[𝓝 (chart y)] fun _ => 1

variable {J} {X : Type*} [TopologicalSpace X]

def Patch.Compatible (p : Patch J X (N := N)) (f : X → N) : Prop :=
  MapsTo f p.core p.plateau

variable [FiniteDimensional ℝ G] [J.Boundaryless] [IsManifold J ∞ N]
  [CompactSpace X] [T2Space X]

/-- Every original source point lies in the interior of a compatible compact core. -/
theorem exists_patch_at {f : X → N} (hf : Continuous f) (x : X) :
    ∃ p : Patch J X (N := N), p.Compatible f ∧ x ∈ interior p.core := by
  let c := NoExoticSixSphere.modelChartPartialDiffeomorph (I := J) (f x)
  have hcx : f x ∈ c.source := mem_extChartAt_source _
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (c.open_target.mem_nhds (c.map_source' hcx))
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
    cutoff_support := hsupport.trans hball
    plateau := O
    plateau_open := hO
    plateau_source := inter_subset_left
    plateau_one := by
      intro y hy
      filter_upwards [hW.mem_nhds hy.2] with z hz
      exact hone hz }
  exact ⟨p, hCO, hxC (mem_singleton x)⟩

end Wikipedia.SmoothSixDPoincare.NativeTransversality
