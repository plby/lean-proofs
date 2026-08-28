import Wikipedia.NoExoticSixSphere.SpanningDiskAffineCollar
import Wikipedia.NoExoticSixSphere.CompactThickeningAvoidance

/-!
# A single thin radial product whose whole interior misses the old ambient space

The exact collar height proves avoidance near the boundary without restricting
the transverse vector. The complementary compact subdisk admits a uniform
positive transverse radius by continuity and the actual disk's core avoidance.
The final radius is no larger than that of the given framed embedded product.
-/

noncomputable section

open Function Set Metric
open scoped Manifold ContDiff

namespace NoExoticSixSphere.StabilizedSpanningDisk.DiskData

open GLOrthonormalization

theorem exists_affine_interior_avoids {N k q : ℕ} {b : Sphere 3}
    {f : Sphere 3 → Vector N} (D : DiskData b f)
    {T : Vector 4 → Vector k →L[ℝ] Vector (N + 6)}
    (A : DiskThickening.FramedProduct D.toFun T q)
    (hCb : ∀ s v, appendZeroMap N 6 (boundaryComplementOperator A.transverse s v) =
      A.transverse s.val v)
    (r : ℝ) (hr : (1 / 2 : ℝ) < r) (hr1 : r < 1)
    (hc : ∀ x ∈ closedBall (0 : Vector 4) 1, r ≤ ‖x‖ →
      D.toFun x = collar b f x ∧
      A.transverse x = A.transverse (SphereRadialRetraction.retract b x).val) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ A.radius ∧
      ∀ x ∈ ball (0 : Vector 4) 1, ∀ v ∈ closedBall (0 : Vector q) ε,
        DiskThickening.map D.toFun A.transverse (x, v) ∉ range (appendZeroMap N 6) := by
  have hL : IsClosed (range (appendZeroMap N 6)) :=
    (appendZeroMap N 6).range.closed_of_finiteDimensional
  obtain ⟨ε, hε, hεavoid⟩ := DiskThickening.exists_avoiding_closed_product
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
    exact D.affine_radial_collar_avoids A hCb hx (hr.trans_le hrx) hxc.1 hxc.2 v

end NoExoticSixSphere.StabilizedSpanningDisk.DiskData
