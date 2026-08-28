import Wikipedia.NoExoticSixSphere.PuncturedUnitBall
import Wikipedia.NoExoticSixSphere.ManifoldPuncturedBoundaryMaps

/-!
# Actual punctured manifold balls and their local sphere classes

The original chart identifies the punctured open region with the actual
punctured Euclidean ball. The resulting sphere homotopy equivalence has an
explicit half-radius inverse. The radial push sends this inverse exactly to
the original linking-sphere parametrization.
-/

noncomputable section

open Set Function Metric Topology ContinuousMap
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereFamily.ParityBall

open GLOrthonormalization

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  {g : ℝ → Sphere 3 → M} {q : ℝ × Sphere 3} (B : ParityBall g q)

def puncturedOpenRegion : Set (ℝ × Sphere 3) := B.openRegion \ {q}

theorem coord_mem_ball {y : ℝ × Sphere 3} (hy : y ∈ B.openRegion) :
    B.chart.symm y ∈ ball (0 : Vector 4) 1 := by
  obtain ⟨z, hz, rfl⟩ := hy
  have he : B.chart.symm (B.chart z) = z :=
    B.chart.left_inv (B.ball_source (ball_subset_closedBall hz))
  rwa [he]

def puncturedChartHomeomorph : B.puncturedOpenRegion ≃ₜ PuncturedUnitBall.Space where
  toFun y := ⟨B.chart.symm y.val, by
    refine ⟨?_, B.coord_ne_zero (B.openRegion_subset_closedRegion y.property.1) y.property.2⟩
    simpa only [mem_ball, dist_zero_right] using B.coord_mem_ball y.property.1⟩
  invFun z := ⟨B.chart z.val, by
    have hz : z.val ∈ ball (0 : Vector 4) 1 := by
      simpa only [mem_ball, dist_zero_right] using z.property.1
    refine ⟨⟨z.val, hz, rfl⟩, ?_⟩
    intro he
    exact z.property.2 (B.chart.injOn (B.ball_source (ball_subset_closedBall hz))
      (B.ball_source (mem_closedBall_self zero_le_one)) (he.trans B.center.symm))⟩
  left_inv y := Subtype.ext (B.chart.right_inv (B.closedRegion_subset_chart_target
    (B.openRegion_subset_closedRegion y.property.1)))
  right_inv z := by
    apply Subtype.ext
    apply B.chart.left_inv
    apply B.ball_source
    apply ball_subset_closedBall
    simpa only [mem_ball, dist_zero_right] using z.property.1
  continuous_toFun := by
    have hc : Continuous (fun y : B.puncturedOpenRegion ↦ B.chart.symm y.val) :=
      (B.chart.contMDiffOn_invFun.continuousOn.mono
        (fun _ hy ↦ B.closedRegion_subset_chart_target
          (B.openRegion_subset_closedRegion hy.1))).domRestrict
    exact hc.subtype_mk _
  continuous_invFun := by
    have hc : ContinuousOn B.chart {z : Vector 4 | ‖z‖ < 1 ∧ z ≠ 0} := by
      apply B.chart.contMDiffOn_toFun.continuousOn.mono
      intro z hz
      apply B.ball_source
      apply ball_subset_closedBall
      simpa only [mem_ball, dist_zero_right] using hz.1
    exact hc.domRestrict.subtype_mk _

def puncturedSphereEquiv : B.puncturedOpenRegion ≃ₕ Sphere 3 :=
  B.puncturedChartHomeomorph.toHomotopyEquiv.trans PuncturedUnitBall.sphereEquiv

theorem puncturedSphereEquiv_apply (y : B.puncturedOpenRegion) :
    (B.puncturedSphereEquiv y).val = ‖B.chart.symm y.val‖⁻¹ • B.chart.symm y.val := rfl

theorem puncturedSphereEquiv_symm_apply (s : Sphere 3) :
    (B.puncturedSphereEquiv.symm s).val = B.chart ((1 / 2 : ℝ) • s.val) := rfl

theorem push_puncturedSphereEquiv_symm (s : Sphere 3) :
    B.push (B.puncturedSphereEquiv.symm s).val = B.boundaryMap s := by
  have hy := (B.puncturedSphereEquiv.symm s).property
  rw [push, if_pos (B.openRegion_subset_closedRegion hy.1)]
  have hs : ‖s.val‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using s.property
  have hn : ‖(1 / 2 : ℝ) • s.val‖ = 1 / 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), hs]
    simp
  have hb : (1 / 2 : ℝ) • s.val ∈ closedBall (0 : Vector 4) 1 := by
    simpa only [mem_closedBall, dist_zero_right, hn] using (by norm_num : (1 / 2 : ℝ) ≤ 1)
  have he : B.chart.symm (B.chart ((1 / 2 : ℝ) • s.val)) = (1 / 2 : ℝ) • s.val :=
    B.chart.left_inv (B.ball_source hb)
  change B.chart (‖B.chart.symm (B.chart ((1 / 2 : ℝ) • s.val))‖⁻¹ •
    B.chart.symm (B.chart ((1 / 2 : ℝ) • s.val))) = B.chart s.val
  rw [he, hn, smul_smul]
  norm_num

end NoExoticSixSphere.SphereFamily.ParityBall
