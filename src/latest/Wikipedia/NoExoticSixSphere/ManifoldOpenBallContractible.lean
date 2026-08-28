import Wikipedia.NoExoticSixSphere.ManifoldPuncturedBall

/-!
# The actual open ball region is contractible

The original chart gives a homeomorphism to the ordinary open Euclidean unit
ball, retaining its actual topology. Contractibility comes from convexity of
that actual ball, not from an assumed topology on the manifold region.
-/

noncomputable section

open Set Function Metric Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereFamily.ParityBall

open GLOrthonormalization

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  {g : ℝ → Sphere 3 → M} {q : ℝ × Sphere 3} (B : ParityBall g q)

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

end NoExoticSixSphere.SphereFamily.ParityBall
