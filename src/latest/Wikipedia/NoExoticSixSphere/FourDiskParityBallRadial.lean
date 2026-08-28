import Wikipedia.NoExoticSixSphere.FourDiskParityBall
import Mathlib.Topology.Piecewise

/-!
# Radial pushing in an original four-disk singularity chart

The retained chart pushes its closed ball onto its original linking sphere
away from the center, and fixes everything outside the open ball.
Continuity across the original frontier is proved explicitly.
-/

noncomputable section

open Set Function Metric Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.GenericFourDisk.ParityBall

open GLOrthonormalization

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  {g : Vector 4 → M} {x : Vector 4} {U : Set (Vector 4)} (B : ParityBall g x U)

theorem frontier_closedRegion : frontier B.closedRegion = B.boundaryRegion := by
  have he : closure (closedBall (0 : Vector 4) 1) = closedBall (0 : Vector 4) 1 :=
    isClosed_closedBall.closure_eq
  have hr : B.closedRegion = CurveChart.region B.chart.toOpenPartialHomeomorph.symm
      (closedBall (0 : Vector 4) 1) :=
    (CurveChart.region_eq_image B.chart.toOpenPartialHomeomorph.symm B.ball_source).symm
  rw [hr, CurveChart.frontier_region _
    (he.symm ▸ isCompact_closedBall (0 : Vector 4) 1) (he.symm ▸ B.ball_source),
    frontier_closedBall _ one_ne_zero]
  rfl

theorem closedRegion_subset_chart_target : B.closedRegion ⊆ B.chart.target := by
  rintro y ⟨z, hz, rfl⟩
  exact B.chart.map_source (B.ball_source hz)

theorem coord_mem_closedBall {y : Vector 4} (hy : y ∈ B.closedRegion) :
    B.chart.symm y ∈ closedBall (0 : Vector 4) 1 := by
  obtain ⟨z, hz, rfl⟩ := hy
  have he : B.chart.symm (B.chart z) = z := B.chart.left_inv (B.ball_source hz)
  rwa [he]

theorem coord_ne_zero {y : Vector 4} (hy : y ∈ B.closedRegion) (hne : y ≠ x) :
    B.chart.symm y ≠ 0 := by
  intro he
  have hi : B.chart (B.chart.symm y) = y :=
    B.chart.right_inv (B.closedRegion_subset_chart_target hy)
  rw [he, B.center] at hi
  exact hne hi.symm

def radialValue (y : Vector 4) : Vector 4 :=
  B.chart (‖B.chart.symm y‖⁻¹ • B.chart.symm y)

theorem radialValue_mem_boundary {y : Vector 4}
    (hy : y ∈ B.closedRegion) (hne : y ≠ x) : B.radialValue y ∈ B.boundaryRegion := by
  refine ⟨‖B.chart.symm y‖⁻¹ • B.chart.symm y, ?_, rfl⟩
  simp only [mem_sphere, dist_zero_right, norm_smul, norm_inv, norm_norm]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr (B.coord_ne_zero hy hne))

theorem radialValue_eq_of_boundary {y : Vector 4} (hy : y ∈ B.boundaryRegion) :
    B.radialValue y = y := by
  obtain ⟨z, hz, rfl⟩ := hy
  have he : B.chart.symm (B.chart z) = z :=
    B.chart.left_inv (B.ball_source (sphere_subset_closedBall hz))
  have hn : ‖z‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hz
  simp only [radialValue, he, hn, inv_one, one_smul]

theorem continuousOn_radialValue :
    ContinuousOn B.radialValue ({x}ᶜ ∩ B.closedRegion) := by
  have hc : ContinuousOn B.chart.symm ({x}ᶜ ∩ B.closedRegion) :=
    B.chart.contMDiffOn_invFun.continuousOn.mono
      (inter_subset_right.trans B.closedRegion_subset_chart_target)
  have hn : ∀ y ∈ {x}ᶜ ∩ B.closedRegion, ‖B.chart.symm y‖ ≠ 0 :=
    fun _ hy ↦ norm_ne_zero_iff.mpr (B.coord_ne_zero hy.2 hy.1)
  have hv := (hc.norm.inv₀ hn).smul hc
  apply B.chart.contMDiffOn_toFun.continuousOn.comp hv
  intro y hy
  apply B.ball_source
  apply sphere_subset_closedBall
  simp only [mem_sphere, dist_zero_right]
  change ‖‖B.chart.symm y‖⁻¹ • B.chart.symm y‖ = 1
  exact norm_smul_inv_norm (B.coord_ne_zero hy.2 hy.1)

def push (y : Vector 4) : Vector 4 := by
  classical
  exact if y ∈ B.closedRegion then B.radialValue y else y

theorem continuousOn_push : ContinuousOn B.push ({x}ᶜ) := by
  classical
  apply ContinuousOn.if
  · intro y hy
    exact B.radialValue_eq_of_boundary (B.frontier_closedRegion ▸ hy.2)
  · change ContinuousOn B.radialValue ({x}ᶜ ∩ closure B.closedRegion)
    rw [B.isCompact_closedRegion.isClosed.closure_eq]
    exact B.continuousOn_radialValue
  · exact continuous_id.continuousOn

theorem push_eq_of_notMem_openRegion {y : Vector 4} (hy : y ∉ B.openRegion) :
    B.push y = y := by
  classical
  by_cases hc : y ∈ B.closedRegion
  · rw [push, if_pos hc]
    apply B.radialValue_eq_of_boundary
    rw [← B.closedRegion_sdiff_openRegion]
    exact ⟨hc, hy⟩
  · exact if_neg hc

theorem push_mem_boundary_of_mem {y : Vector 4}
    (hy : y ∈ B.closedRegion) (hne : y ≠ x) : B.push y ∈ B.boundaryRegion := by
  rw [push, if_pos hy]
  exact B.radialValue_mem_boundary hy hne

theorem push_notMem_openRegion {y : Vector 4} (hne : y ≠ x) :
    B.push y ∉ B.openRegion := by
  by_cases hc : y ∈ B.closedRegion
  · have hb := B.push_mem_boundary_of_mem hc hne
    rw [← B.closedRegion_sdiff_openRegion] at hb
    exact hb.2
  · rw [B.push_eq_of_notMem_openRegion (fun ho ↦ hc (B.openRegion_subset_closedRegion ho))]
    exact fun ho ↦ hc (B.openRegion_subset_closedRegion ho)

end NoExoticSixSphere.GenericFourDisk.ParityBall
