import Wikipedia.NoExoticSixSphere.ManifoldParityBall
import Mathlib.Topology.Piecewise

/-!
# Continuous radial pushing in an actual parity-ball chart

On the complement of the actual center, the map pushes the closed ball onto
its linking sphere and fixes the complement of its open interior. Continuity
is proved across the actual frontier using the retained partial diffeomorphism.
-/

noncomputable section

open Set Function Metric Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereFamily.ParityBall

open GLOrthonormalization

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  {g : ℝ → Sphere 3 → M} {q : ℝ × Sphere 3} (B : ParityBall g q)

theorem closedRegion_subset_chart_target : B.closedRegion ⊆ B.chart.target := by
  rintro y ⟨z, hz, rfl⟩
  exact B.chart.map_source (B.ball_source hz)

theorem coord_mem_closedBall {y : ℝ × Sphere 3} (hy : y ∈ B.closedRegion) :
    B.chart.symm y ∈ closedBall (0 : Vector 4) 1 := by
  obtain ⟨z, hz, rfl⟩ := hy
  have he : B.chart.symm (B.chart z) = z := B.chart.left_inv (B.ball_source hz)
  rwa [he]

theorem coord_ne_zero {y : ℝ × Sphere 3} (hy : y ∈ B.closedRegion) (hne : y ≠ q) :
    B.chart.symm y ≠ 0 := by
  intro he
  have hi : B.chart (B.chart.symm y) = y :=
    B.chart.right_inv (B.closedRegion_subset_chart_target hy)
  rw [he, B.center] at hi
  exact hne hi.symm

def radialValue (y : ℝ × Sphere 3) : ℝ × Sphere 3 :=
  B.chart (‖B.chart.symm y‖⁻¹ • B.chart.symm y)

theorem radialValue_mem_boundary {y : ℝ × Sphere 3}
    (hy : y ∈ B.closedRegion) (hne : y ≠ q) : B.radialValue y ∈ B.boundaryRegion := by
  refine ⟨‖B.chart.symm y‖⁻¹ • B.chart.symm y, ?_, rfl⟩
  simp only [mem_sphere, dist_zero_right, norm_smul, norm_inv, norm_norm]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr (B.coord_ne_zero hy hne))

theorem radialValue_eq_of_boundary {y : ℝ × Sphere 3} (hy : y ∈ B.boundaryRegion) :
    B.radialValue y = y := by
  obtain ⟨z, hz, rfl⟩ := hy
  have he : B.chart.symm (B.chart z) = z :=
    B.chart.left_inv (B.ball_source (sphere_subset_closedBall hz))
  have hn : ‖z‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hz
  simp only [radialValue, he, hn, inv_one, one_smul]

theorem continuousOn_radialValue :
    ContinuousOn B.radialValue ({q}ᶜ ∩ B.closedRegion) := by
  have hc : ContinuousOn B.chart.symm ({q}ᶜ ∩ B.closedRegion) :=
    B.chart.contMDiffOn_invFun.continuousOn.mono
      (inter_subset_right.trans B.closedRegion_subset_chart_target)
  have hn : ∀ y ∈ {q}ᶜ ∩ B.closedRegion, ‖B.chart.symm y‖ ≠ 0 :=
    fun _ hy ↦ norm_ne_zero_iff.mpr (B.coord_ne_zero hy.2 hy.1)
  have hv := (hc.norm.inv₀ hn).smul hc
  apply B.chart.contMDiffOn_toFun.continuousOn.comp hv
  intro y hy
  apply B.ball_source
  apply sphere_subset_closedBall
  simp only [mem_sphere, dist_zero_right]
  change ‖‖B.chart.symm y‖⁻¹ • B.chart.symm y‖ = 1
  exact norm_smul_inv_norm (B.coord_ne_zero hy.2 hy.1)

def push (y : ℝ × Sphere 3) : ℝ × Sphere 3 := by
  classical
  exact if y ∈ B.closedRegion then B.radialValue y else y

theorem continuousOn_push : ContinuousOn B.push ({q}ᶜ) := by
  classical
  apply ContinuousOn.if
  · intro y hy
    exact B.radialValue_eq_of_boundary (B.frontier_closedRegion ▸ hy.2)
  · change ContinuousOn B.radialValue ({q}ᶜ ∩ closure B.closedRegion)
    rw [B.isCompact_closedRegion.isClosed.closure_eq]
    exact B.continuousOn_radialValue
  · exact continuous_id.continuousOn

theorem push_eq_of_notMem_openRegion {y : ℝ × Sphere 3} (hy : y ∉ B.openRegion) :
    B.push y = y := by
  classical
  by_cases hc : y ∈ B.closedRegion
  · rw [push, if_pos hc]
    apply B.radialValue_eq_of_boundary
    rw [← B.closedRegion_sdiff_openRegion]
    exact ⟨hc, hy⟩
  · exact if_neg hc

theorem push_mem_boundary_of_mem {y : ℝ × Sphere 3}
    (hy : y ∈ B.closedRegion) (hne : y ≠ q) : B.push y ∈ B.boundaryRegion := by
  rw [push, if_pos hy]
  exact B.radialValue_mem_boundary hy hne

theorem push_notMem_openRegion {y : ℝ × Sphere 3} (hne : y ≠ q) :
    B.push y ∉ B.openRegion := by
  by_cases hc : y ∈ B.closedRegion
  · have hb := B.push_mem_boundary_of_mem hc hne
    rw [← B.closedRegion_sdiff_openRegion] at hb
    exact hb.2
  · rw [B.push_eq_of_notMem_openRegion (fun ho ↦ hc (B.openRegion_subset_closedRegion ho))]
    exact fun ho ↦ hc (B.openRegion_subset_closedRegion ho)

end NoExoticSixSphere.SphereFamily.ParityBall
