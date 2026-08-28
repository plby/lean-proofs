import Wikipedia.NoExoticSixSphere.FourDiskParityBallRadial
import Wikipedia.NoExoticSixSphere.PuncturedUnitBall

/-!
# Original open disk-chart regions and their punctured sphere models

The retained chart is a homeomorphism from the actual open region to the
Euclidean ball. Removing its actual center gives the actual punctured
ball, whose sphere homotopy inverse is the half-radius original chart map.
-/

noncomputable section

open Set Function Metric Topology ContinuousMap
open scoped Manifold ContDiff

namespace NoExoticSixSphere.GenericFourDisk.ParityBall

open GLOrthonormalization

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  {g : Vector 4 → M} {x : Vector 4} {U : Set (Vector 4)} (B : ParityBall g x U)

def puncturedOpenRegion : Set (Vector 4) := B.openRegion \ {x}

theorem isOpen_puncturedOpenRegion : IsOpen B.puncturedOpenRegion :=
  B.isOpen_openRegion.sdiff isClosed_singleton

theorem coord_mem_ball {y : Vector 4} (hy : y ∈ B.openRegion) :
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

def openChartHomeomorph : B.openRegion ≃ₜ ball (0 : Vector 4) 1 where
  toFun y := ⟨B.chart.symm y.val, B.coord_mem_ball y.property⟩
  invFun z := ⟨B.chart z.val, ⟨z.val, z.property, rfl⟩⟩
  left_inv y := Subtype.ext (B.chart.right_inv (B.closedRegion_subset_chart_target
    (B.openRegion_subset_closedRegion y.property)))
  right_inv z := Subtype.ext
    (B.chart.left_inv (B.ball_source (ball_subset_closedBall z.property)))
  continuous_toFun := by
    have hc : Continuous (fun y : B.openRegion ↦ B.chart.symm y.val) :=
      (B.chart.contMDiffOn_invFun.continuousOn.mono
        (B.openRegion_subset_closedRegion.trans B.closedRegion_subset_chart_target)).domRestrict
    exact hc.subtype_mk _
  continuous_invFun :=
    (B.chart.contMDiffOn_toFun.continuousOn.mono
      (ball_subset_closedBall.trans B.ball_source)).domRestrict.subtype_mk _

theorem openRegion_contractible : ContractibleSpace B.openRegion := by
  let := (convex_ball (0 : Vector 4) 1).contractibleSpace ⟨0, mem_ball_self zero_lt_one⟩
  exact B.openChartHomeomorph.contractibleSpace

end NoExoticSixSphere.GenericFourDisk.ParityBall
