import Wikipedia.NoExoticSixSphere.SphereFamilyBoundaryFrame
import Wikipedia.NoExoticSixSphere.SpanningDiskDimension
import Wikipedia.NoExoticSixSphere.FramedDiskParityCongruence

/-!
# Parity comparison along a jointly smooth framed sphere--disk family

The sphere and its boundary frame may vary. Their actual spanning disks give
the normality condition throughout the parameter cylinder, so the previously
proved immersed-disk comparison identifies the endpoint parities.
-/

noncomputable section

open Function Metric
open scoped Manifold ContDiff

namespace NoExoticSixSphere.StabilizedSpanningDisk.DiskData

open GLOrthonormalization Stiefel ProjectionHomotopy

theorem parity_eq_of_sphere_family {k : ℕ} (b : Sphere 3)
    (f : ℝ → Sphere 3 → Vector (k + 6))
    (hf : ∀ t, ContMDiff (𝓡 3) (𝓡 (k + 6)) ∞ (f t))
    (a : ℝ → Sphere 3 → Space (k + 6) k)
    (has : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3))
      𝓘(ℝ, Vector k →L[ℝ] Vector (k + 6)) ∞ (fun q : ℝ × Sphere 3 ↦ (a q.1 q.2).val))
    (ha : ∀ t : unitInterval, ∀ s,
      (a (t : ℝ) s).val.range ≤ (mfderiv (𝓡 3) (𝓡 (k + 6)) (f (t : ℝ)) s).rangeᗮ)
    (D : ∀ t : unitInterval, DiskData b (f (t : ℝ)))
    (G : ℝ → Vector 4 → Vector (k + 12)) (hG : ContDiff ℝ ∞ (uncurry G))
    (hD : ∀ t : unitInterval, (D t).toFun = G (t : ℝ)) :
    (D 0).parity (hf 0) (a 0) (has.comp (contMDiff_const.prodMk contMDiff_id)) (ha 0) =
      (D 1).parity (hf 1) (a 1) (has.comp (contMDiff_const.prodMk contMDiff_id)) (ha 1) := by
  have hs (t : ℝ) : ContMDiff (𝓡 3)
      𝓘(ℝ, Vector k →L[ℝ] Vector (k + 6)) ∞ (fun s ↦ (a t s).val) :=
    has.comp (contMDiff_const.prodMk contMDiff_id)
  let A := boundaryFrameFamily a has
  have hA (q : unitInterval × Sphere 3) :
      (A q).val.range ≤ (fderiv ℝ (G (q.1 : ℝ)) q.2.val).rangeᗮ := by
    rw [← hD q.1]
    exact (D q.1).normal_boundaryFrameMap (hf q.1) (a q.1) (hs q.1) (ha q.1) q.2
  have hi (t : unitInterval) (x : Vector 4) (hx : x ∈ closedBall 0 1) :
      Injective (fderiv ℝ (G (t : ℝ)) x) := by
    rw [← hD t]
    exact (D t).immersive x hx
  have hAt (t : unitInterval) : slice A t = boundaryFrameMap (a (t : ℝ)) (hs t) := by
    exact boundaryFrameFamily_slice a has t
  have h := DiskHomotopy.parity_endpoints (k + 3) G hG hi A hA
  have h₀ := (D 0).parity_eq_of_map_and_frame (hf 0) (a 0) (hs 0) (ha 0) (G 0)
    (fun _ _ ↦ (DiskHomotopy.contDiff_slice (k + 3) G hG 0).contDiffAt)
    (hi 0) (slice A 0) (fun s ↦ hA (0, s)) (hD 0) (hAt 0).symm
  have h₁ := (D 1).parity_eq_of_map_and_frame (hf 1) (a 1) (hs 1) (ha 1) (G 1)
    (fun _ _ ↦ (DiskHomotopy.contDiff_slice (k + 3) G hG 1).contDiffAt)
    (hi 1) (slice A 1) (fun s ↦ hA (1, s)) (hD 1) (hAt 1).symm
  exact h₀.trans (h.trans h₁.symm)

theorem parityOfDimension_eq_of_sphere_family {N k : ℕ} (hN : N = k + 6) (b : Sphere 3)
    (f : ℝ → Sphere 3 → Vector N) (hf : ∀ t, ContMDiff (𝓡 3) (𝓡 N) ∞ (f t))
    (a : ℝ → Sphere 3 → Space N k)
    (has : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3))
      𝓘(ℝ, Vector k →L[ℝ] Vector N) ∞ (fun q : ℝ × Sphere 3 ↦ (a q.1 q.2).val))
    (ha : ∀ t : unitInterval, ∀ s,
      (a (t : ℝ) s).val.range ≤ (mfderiv (𝓡 3) (𝓡 N) (f (t : ℝ)) s).rangeᗮ)
    (D : ∀ t : unitInterval, DiskData b (f (t : ℝ)))
    (G : ℝ → Vector 4 → Vector (N + 6)) (hG : ContDiff ℝ ∞ (uncurry G))
    (hD : ∀ t : unitInterval, (D t).toFun = G (t : ℝ)) :
    (D 0).parityOfDimension hN (hf 0) (a 0)
        (has.comp (contMDiff_const.prodMk contMDiff_id)) (ha 0) =
      (D 1).parityOfDimension hN (hf 1) (a 1)
        (has.comp (contMDiff_const.prodMk contMDiff_id)) (ha 1) := by
  subst N
  exact parity_eq_of_sphere_family b f hf a has ha D G hG hD

end NoExoticSixSphere.StabilizedSpanningDisk.DiskData
