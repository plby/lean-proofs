import Wikipedia.HopfProblem.DegreeCollapseLowRadialTransverseProduct
import Wikipedia.HopfProblem.DegreeCollapseLowAffineDiskCollar
import Wikipedia.HopfProblem.DegreeCollapseLowCoreProduct

/-!

# The entire low-surgery interior product avoids the original ambient space

The exact collar height handles its whole boundary annulus for every
transverse vector. Compactness supplies one uniform radius for the remaining
inner subdisk. The minimum radius therefore protects every interior point
of the actual product, not only its core.
-/

noncomputable section

open Function Set Metric
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.LowSurgery

open NoExoticSixSphere GLOrthonormalization Stiefel StabilizedSpanningDisk

variable {d : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  (e : EuclideanEmbedding 7 M)
  (a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel)
  (f : NoExoticSixSphere.Sphere d → M) (hf : ContMDiff (𝓡 d) (𝓡 7) ∞ f)
  (hd : ∀ s, Injective (mfderiv (𝓡 d) (𝓡 7) f s))
  {b : NoExoticSixSphere.Sphere d}
  (D : FramedDisk b (e.toFun ∘ f) (fun s => a.orthonormal (f s)))
  (A : LowFramedProduct.FramedProduct (q := 7 - d) D.map D.frame)

include hf hd in
theorem exists_thickening_interior_avoids (r : ℝ) (hr : (1 / 2 : ℝ) < r) (hr1 : r < 1)
    (hc : ∀ x ∈ closedBall (0 : Vector (d + 1)) 1, r ≤ ‖x‖ →
      D.map x = collar b (e.toFun ∘ f) x ∧
      A.transverse x = A.transverse (SphereRadialRetraction.retract b x).val) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ A.radius ∧
      ∀ x ∈ ball (0 : Vector (d + 1)) 1, ∀ v ∈ closedBall (0 : Vector (7 - d)) ε,
        LowDiskThickening.map D.map A.transverse (x, v) ∉
          range (appendZeroMap e.ambientDimension (1 + (1 + (d + 1)))) := by
  have hL : IsClosed (range (appendZeroMap e.ambientDimension (1 + (1 + (d + 1))))) :=
    (appendZeroMap e.ambientDimension (1 + (1 + (d + 1)))).range.closed_of_finiteDimensional
  obtain ⟨ε, hε, hεavoid⟩ := LowDiskThickening.exists_avoiding_closed_product
    (isCompact_closedBall (0 : Vector (d + 1)) r) D.map A.transverse
    (fun _ _ ↦ D.smooth.contDiffAt)
    (fun x hx ↦ A.smooth_transverse x ((closedBall_subset_closedBall hr1.le) hx)) hL
    (fun x hx ↦ D.interior_avoids x ((closedBall_subset_ball hr1) hx))
  refine ⟨min ε A.radius, lt_min hε A.radius_pos, min_le_right _ _, ?_⟩
  intro x hx v hv
  rcases le_total ‖x‖ r with hxr | hrx
  · have hxK : x ∈ closedBall (0 : Vector (d + 1)) r := by
      simpa only [mem_closedBall, dist_zero_right] using hxr
    exact hεavoid x hxK v ((closedBall_subset_closedBall (min_le_left _ _)) hv)
  · have hxc := hc x (ball_subset_closedBall hx) hrx
    exact thickening_radial_collar_avoids e a f hf hd D A hx (hr.trans_le hrx)
      hxc.1 hxc.2 v

end Wikipedia.HopfProblem.DegreeCollapse.LowSurgery

