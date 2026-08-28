import Wikipedia.NoExoticSixSphere.FourComplementDiskNormalFrame
import Wikipedia.NoExoticSixSphere.SpanningDiskCollaredNormalFrame

/-!
# Collared normal frames for three-sphere surgery in dimension seven

The original boundary frame leaves four complementary normal directions
on the actual stabilized spanning four-disk. Native Stiefel connectivity
therefore constructs its extension without a parity hypothesis. Relative
collar straightening retains the original radial map and normal columns
on a whole annulus.

This constructs the framed disk, not an attached surgery trace.
-/

noncomputable section

open Set Metric Function
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.StabilizedSpanningDisk.DiskData

open GLOrthonormalization Stiefel

theorem exists_normalFrame_collar_of_dimension_seven {N k : ℕ}
    {b : Sphere 3} {f : Sphere 3 → Vector N} (D : DiskData b f)
    (hf : ContMDiff (𝓡 3) (𝓡 N) ∞ f) (hN : N = k + 7)
    (a : Sphere 3 → Space N k)
    (has : ContMDiff (𝓡 3) 𝓘(ℝ, Vector k →L[ℝ] Vector N) ∞ (fun s ↦ (a s).val))
    (ha : ∀ s, (a s).val.range ≤ (mfderiv (𝓡 3) (𝓡 N) f s).rangeᗮ) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      ∃ T : Vector 4 → Vector (k + 5) →L[ℝ] Vector (N + 6),
        (∀ x ∈ closedBall (0 : Vector 4) 1, ContDiffAt ℝ ∞ T x) ∧
        (∀ x ∈ closedBall (0 : Vector 4) 1, ∀ w, ‖T x w‖ = ‖w‖) ∧
        (∀ x ∈ closedBall (0 : Vector 4) 1,
          (T x).range ≤ (fderiv ℝ D.toFun x).rangeᗮ) ∧
        (∀ s : Sphere 3, T s.val = boundaryFrameOperator (a s).val) ∧
        ∀ x ∈ closedBall (0 : Vector 4) 1, r ≤ ‖x‖ →
          D.toFun x = collar b f x ∧
          T x = boundaryFrameOperator (a (SphereRadialRetraction.retract b x)).val := by
  have hab (s : Sphere 3) :
      ((boundaryFrameMap a has) s).val.range ≤ (fderiv ℝ D.toFun s.val).rangeᗮ := by
    obtain ⟨V, hV, hSV, heq⟩ := D.collar_eq
    exact boundaryFrame_normal_disk b f hf a ha hV hSV heq s
  obtain ⟨T, hTs, hTn, hTr, hTb⟩ := exists_smoothDiskNormalFrame_of_complement
    (by decide : 3 < 4) D.toFun (fun _ _ ↦ D.smooth.contDiffAt) D.immersive
    (by omega : N + 6 = 4 + (4 + (k + 5))) (boundaryFrameMap a has)
    (contMDiff_boundaryFrameOperator has) hab
  exact D.exists_normalFrame_collar hf a has ha T hTs hTn hTr hTb

end NoExoticSixSphere.StabilizedSpanningDisk.DiskData
