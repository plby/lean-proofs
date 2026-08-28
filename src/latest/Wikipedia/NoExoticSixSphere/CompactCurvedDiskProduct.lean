import Wikipedia.NoExoticSixSphere.CompactSphereTubeDifference
import Wikipedia.NoExoticSixSphere.RadialCollarCorrectionJet
import Wikipedia.NoExoticSixSphere.SpanningDiskAffineCollar

/-!
# The actual curved attaching map from the compact-image tube

The supported old-coordinate correction fixes the disk core and its actual
derivative, preserves interior avoidance, and replaces the radial affine face
by the original-manifold tube on the whole outer collar. No compactness of
the ambient manifold or global tubular retraction is assumed.
-/

noncomputable section

open Function Set Metric
open scoped Manifold ContDiff
open Wikipedia.SmoothSixDPoincare.SphereBoundary

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization Stiefel StabilizedSpanningDisk

variable {n k q : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  (e : EuclideanEmbedding n M) (f : Sphere 3 → M)
  {b : Sphere 3} (D : DiskData b (e.toFun ∘ f))
  {T : Vector 4 → Vector k →L[ℝ] Vector (e.ambientDimension + 6)}
  (A : DiskThickening.FramedProduct D.toFun T q) (R : e.RetractionNear (range f))
  (χ : ContDiffBump (0 : Vector 4))

def compactCurvedDiskProduct (p : Vector 4 × Vector q) : Vector (e.ambientDimension + 6) :=
  DiskThickening.map D.toFun A.transverse p + appendZeroMap e.ambientDimension 6
    (RadialCollarCorrection.correction χ b
      (e.compactSphereTubeDifference f (boundaryComplementOperator A.transverse) R) p)

theorem compactCurvedDiskProduct_core (x : Vector 4) :
    e.compactCurvedDiskProduct f D A R χ (x, 0) = D.toFun x := by
  rw [compactCurvedDiskProduct, RadialCollarCorrection.correction_core χ b _
    (e.compactSphereTubeDifference_core f (boundaryComplementOperator A.transverse) R),
    map_zero, add_zero, DiskThickening.map_core]

theorem compactCurvedDiskProduct_eq_affine {x : Vector 4}
    (hx : x ∈ closedBall (0 : Vector 4) χ.rIn) (v : Vector q) :
    e.compactCurvedDiskProduct f D A R χ (x, v) =
      DiskThickening.map D.toFun A.transverse (x, v) := by
  rw [compactCurvedDiskProduct, RadialCollarCorrection.correction_eq_zero χ b _ hx,
    map_zero, add_zero]

theorem compactCurvedDiskProduct_avoids {p : Vector 4 × Vector q}
    (hp : DiskThickening.map D.toFun A.transverse p ∉ range (appendZeroMap e.ambientDimension 6)) :
    e.compactCurvedDiskProduct f D A R χ p ∉ range (appendZeroMap e.ambientDimension 6) := by
  rintro ⟨y, hy⟩
  let w := RadialCollarCorrection.correction χ b
    (e.compactSphereTubeDifference f (boundaryComplementOperator A.transverse) R) p
  apply hp
  refine ⟨y - w, ?_⟩
  rw [map_sub, hy]
  change (DiskThickening.map D.toFun A.transverse p + appendZeroMap e.ambientDimension 6 w) -
    appendZeroMap e.ambientDimension 6 w = _
  exact add_sub_cancel_right _ _

variable (hf : ContMDiff (𝓡 3) (𝓡 n) ∞ f)

include hf in
theorem contDiffAt_compactCurvedDiskProduct {x : Vector 4}
    (hx : x ∈ closedBall (0 : Vector 4) 1) (v : Vector q)
    (hp : (SphereRadialRetraction.retract b x, v) ∈
      e.compactSphereTubeDomain f (boundaryComplementOperator A.transverse) R) :
    ContDiffAt ℝ ∞ (e.compactCurvedDiskProduct f D A R χ) (x, v) := by
  have hH := DiskThickening.contDiffAt_map D.toFun A.transverse x v
    D.smooth.contDiffAt (A.smooth_transverse x hx)
  have hc := RadialCollarCorrection.contDiffAt_correction χ b
    (e.compactSphereTubeDifference f (boundaryComplementOperator A.transverse) R) x v
      (e.contMDiffAt_compactSphereTubeDifference f (boundaryComplementOperator A.transverse)
        R hf (contMDiff_boundaryComplementOperator A.transverse A.smooth_transverse) hp)
  exact hH.add ((appendZeroMap e.ambientDimension 6).contDiff.contDiffAt.comp (x, v) hc)

include hf in
theorem fderiv_compactCurvedDiskProduct_core
    (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 n) f s))
    (hiC : ∀ s, Injective (boundaryComplementOperator A.transverse s))
    (hCr : ∀ s, (boundaryComplementOperator A.transverse s).range = e.sphereNormalSpace f s)
    {x : Vector 4} (hx : x ∈ closedBall (0 : Vector 4) 1) :
    fderiv ℝ (e.compactCurvedDiskProduct f D A R χ) (x, 0) =
      fderiv ℝ (DiskThickening.map D.toFun A.transverse) (x, 0) := by
  let C := boundaryComplementOperator A.transverse
  have hCs := contMDiff_boundaryComplementOperator A.transverse A.smooth_transverse
  let g := e.compactSphereTubeDifference f C R
  have hgs (s : Sphere 3) : ContMDiffAt ((𝓡 3).prod (𝓡 q)) (𝓡 e.ambientDimension) ∞
      g (s, 0) := e.contMDiffAt_compactSphereTubeDifference f C R hf hCs
    (e.core_mem_compactSphereTubeDomain f C R s)
  have hgj (s : Sphere 3) :
      mfderiv ((𝓡 3).prod (𝓡 q)) (𝓡 e.ambientDimension) g (s, 0) = 0 :=
    e.mfderiv_compactSphereTubeDifference_core f C R hf hCs hd hiC hCr s
  have hc := (RadialCollarCorrection.contDiffAt_correction χ b g x 0
    (hgs (SphereRadialRetraction.retract b x))).differentiableAt (by simp)
  have hj := RadialCollarCorrection.fderiv_correction_core χ b g hgs
    (e.compactSphereTubeDifference_core f C R) hgj x
  have hc' := hc.hasFDerivAt
  rw [hj] at hc'
  have hH := (DiskThickening.contDiffAt_map D.toFun A.transverse x 0
    D.smooth.contDiffAt (A.smooth_transverse x hx)).differentiableAt (by simp)
  have he := (hH.hasFDerivAt.add
    ((appendZeroMap e.ambientDimension 6).hasFDerivAt.comp (x, 0) hc')).fderiv
  change fderiv ℝ (e.compactCurvedDiskProduct f D A R χ) (x, 0) = _ at he
  simpa only [ContinuousLinearMap.comp_zero, add_zero] using he

theorem compactCurvedDiskProduct_collar
    (hCb : ∀ s v, appendZeroMap e.ambientDimension 6
      (boundaryComplementOperator A.transverse s v) = A.transverse s.val v)
    {x : Vector 4} (hx : (1 / 2 : ℝ) < ‖x‖)
    (hDx : D.toFun x = collar b (e.toFun ∘ f) x)
    (hCx : A.transverse x = A.transverse (SphereRadialRetraction.retract b x).val)
    (hχ : χ.rOut ≤ ‖x‖) (v : Vector q) :
    e.compactCurvedDiskProduct f D A R χ (x, v) = coordinates e.ambientDimension 4
      ((e.toFun (e.compactSphereTube f (boundaryComplementOperator A.transverse) R
        (SphereRadialRetraction.retract b x, v)), definingFunction x), 0) := by
  let s := SphereRadialRetraction.retract b x
  let C := boundaryComplementOperator A.transverse
  rw [compactCurvedDiskProduct, D.affine_radial_collar A hCb hx hDx hCx v,
    RadialCollarCorrection.correction_eq_radial χ b _ hχ]
  rw [← coordinates_old e.ambientDimension 4
    (e.compactSphereTubeDifference f C R (s, v)), ← map_add]
  simp only [Prod.mk_add_mk, add_zero]
  change coordinates e.ambientDimension 4
    ((e.ambientSphereTube f C (s, v) + e.compactSphereTubeDifference f C R (s, v),
      definingFunction x), 0) = _
  rw [e.ambientSphereTube_add_compactDifference f C R]

theorem compactCurvedDiskProduct_boundary
    (hCb : ∀ s v, appendZeroMap e.ambientDimension 6
      (boundaryComplementOperator A.transverse s v) = A.transverse s.val v)
    (hχ : χ.rOut ≤ 1) (s : Sphere 3) (v : Vector q) :
    e.compactCurvedDiskProduct f D A R χ (s.val, v) = appendZeroMap e.ambientDimension 6
      (e.toFun (e.compactSphereTube f (boundaryComplementOperator A.transverse) R (s, v))) := by
  have hDx : D.toFun s.val = collar b (e.toFun ∘ f) s.val := by
    obtain ⟨V, _, hSV, hDV⟩ := D.collar_eq
    exact hDV (hSV s.property)
  have hCx : A.transverse s.val = A.transverse (SphereRadialRetraction.retract b s.val).val := by
    rw [SphereRadialRetraction.retract_coe]
  have hhalf : (1 / 2 : ℝ) < ‖s.val‖ := by rw [ClosedHemisphere.unit_norm]; norm_num
  have hχs : χ.rOut ≤ ‖s.val‖ := by rw [ClosedHemisphere.unit_norm]; exact hχ
  rw [e.compactCurvedDiskProduct_collar f D A R χ hCb hhalf hDx hCx hχs v,
    SphereRadialRetraction.retract_coe,
    (definingFunction_eq_zero_iff s.val).mpr s.property, coordinates_old]

end NoExoticSixSphere.EuclideanEmbedding
