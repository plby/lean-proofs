import Wikipedia.HopfProblem.DegreeCollapseSevenRadialTransverseProduct
import Wikipedia.HopfProblem.DegreeCollapseSevenAffineDiskCollar
import Wikipedia.HopfProblem.DegreeCollapseGeneralCoreProduct

/-!
# SevenWholeProductAvoidance

The entire thin interior product avoids the old ambient plane. The exact collar height handles the boundary annulus for every transverse vector, and compactness supplies uniform avoidance on the remaining subdisk.
-/

noncomputable section

open Function Set Metric
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery

open NoExoticSixSphere GLOrthonormalization Stiefel StabilizedSpanningDisk

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  (e : EuclideanEmbedding 7 M)
  (a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel)
  (f : Sphere 3 → M) (hf : ContMDiff (𝓡 3) (𝓡 7) ∞ f)
  (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 7) f s))
  {b : Sphere 3} (D : DiskData b (e.toFun ∘ f))
  {T : Vector 4 → Vector ((e.ambientDimension - 7) + 5) →L[ℝ]
    Vector (e.ambientDimension + 6)}
  (A : EightDimensionalFramedProduct.FramedProduct D.toFun T)
  (hTb : ∀ s : Sphere 3, T s.val = boundaryFrameOperator (SevenSurgery.normalFrameOnSphere e a f s).val)

include a hf hd hTb in
theorem exists_thickening_interior_avoids (r : ℝ) (hr : (1 / 2 : ℝ) < r) (hr1 : r < 1)
    (hc : ∀ x ∈ closedBall (0 : Vector 4) 1, r ≤ ‖x‖ →
      D.toFun x = collar b (e.toFun ∘ f) x ∧
      A.transverse x = A.transverse (SphereRadialRetraction.retract b x).val) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ A.radius ∧
      ∀ x ∈ ball (0 : Vector 4) 1, ∀ v ∈ closedBall (0 : Vector 4) ε,
        GeneralDiskThickening.map D.toFun A.transverse (x, v) ∉
          range (appendZeroMap e.ambientDimension 6) := by
  have hL : IsClosed (range (appendZeroMap e.ambientDimension 6)) :=
    (appendZeroMap e.ambientDimension 6).range.closed_of_finiteDimensional
  obtain ⟨ε, hε, hεavoid⟩ := GeneralDiskThickening.exists_avoiding_closed_product
    (isCompact_closedBall (0 : Vector 4) r) D.toFun A.transverse
    (fun _ _ ↦ D.smooth.contDiffAt)
    (fun x hx ↦ A.smooth_transverse x ((closedBall_subset_closedBall hr1.le) hx)) hL
    (fun x hx ↦ D.avoids x ((closedBall_subset_ball hr1) hx))
  refine ⟨min ε A.radius, lt_min hε A.radius_pos, min_le_right _ _, ?_⟩
  intro x hx v hv
  rcases le_total ‖x‖ r with hxr | hrx
  · have hxK : x ∈ closedBall (0 : Vector 4) r := by
      simpa only [mem_closedBall, dist_zero_right] using hxr
    exact hεavoid x hxK v ((closedBall_subset_closedBall (min_le_left _ _)) hv)
  · have hxc := hc x (ball_subset_closedBall hx) hrx
    exact SevenSurgery.thickening_radial_collar_avoids e a f hf hd D A hTb hx (hr.trans_le hrx)
      hxc.1 hxc.2 v

end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery
