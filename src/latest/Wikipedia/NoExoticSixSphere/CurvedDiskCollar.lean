import Wikipedia.NoExoticSixSphere.CurvedDiskProduct

/-!
# The corrected product has the exact original-manifold attaching face

On the outer collar the corrected map is the actual embedded retracted tube
with the prescribed normal height and zero graph coordinates. On the whole
boundary face the height is zero, so this is exactly the stabilization of
the original-manifold tube, not merely agreement to first order at its core.
-/

noncomputable section

open Function
open scoped Manifold ContDiff
open Wikipedia.SmoothSixDPoincare.SphereBoundary

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization Stiefel StabilizedSpanningDisk

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (e : EuclideanEmbedding 6 M)
  (a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)
  (f : Sphere 3 → M) (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f)
  (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s))
  {b : Sphere 3} (D : DiskData b (e.toFun ∘ f))
  {T : Vector 4 → Vector ((e.ambientDimension - 6) + 5) →L[ℝ]
    Vector (e.ambientDimension + 6)}
  (A : DiskThickening.FramedProduct D.toFun T) (R : TubularRetraction e)
  (χ : ContDiffBump (0 : Vector 4))
  (hTb : ∀ s : Sphere 3, T s.val = boundaryFrameOperator (e.normalFrameOnSphere a f s).val)

include a hf hd hTb in
theorem curvedDiskProduct_collar {x : Vector 4} (hx : (1 / 2 : ℝ) < ‖x‖)
    (hχ : χ.rOut ≤ ‖x‖) (hDx : D.toFun x = collar b (e.toFun ∘ f) x)
    (hCx : A.transverse x = A.transverse (SphereRadialRetraction.retract b x).val)
    (v : Vector 3) :
    e.curvedDiskProduct f D A R χ (x, v) = coordinates e.ambientDimension 4
      ((e.toFun (e.internalSphereTube f A.boundaryTransverse R
        (SphereRadialRetraction.retract b x, v)), definingFunction x), 0) := by
  rw [curvedDiskProduct, e.thickening_radial_collar a f hf hd D A hTb hx hDx hCx,
    RadialCollarCorrection.correction_eq_radial χ b _ hχ,
    ← coordinates_old e.ambientDimension 4, ← map_add]
  simp only [Prod.mk_add_mk, add_zero]
  rw [e.ambientSphereTube_add_difference]

include a hf hd hTb in
theorem curvedDiskProduct_boundary (hχ : χ.rOut ≤ 1) (s : Sphere 3) (v : Vector 3) :
    e.curvedDiskProduct f D A R χ (s.val, v) = appendZeroMap e.ambientDimension 6
      (e.toFun (e.internalSphereTube f A.boundaryTransverse R (s, v))) := by
  have hχs : χ.rOut ≤ ‖s.val‖ := by rw [ClosedHemisphere.unit_norm]; exact hχ
  rw [curvedDiskProduct, e.thickening_boundary_affine a f hf hd D A hTb,
    RadialCollarCorrection.correction_eq_radial χ b _ hχs,
    SphereRadialRetraction.retract_coe, ← map_add, e.ambientSphereTube_add_difference]

end NoExoticSixSphere.EuclideanEmbedding
