import Wikipedia.HopfProblem.DegreeCollapseSevenSphereTubeDifference
import Wikipedia.HopfProblem.DegreeCollapseGeneralRadialCorrection
import Wikipedia.HopfProblem.DegreeCollapseSevenAffineDiskCollar

/-!
# SevenCurvedDiskProduct

The actual supported correction matches the whole original-manifold attaching face and retains the disk core and its derivative. No embedded product or interior avoidance is inferred merely from the core equations.
-/

noncomputable section

open Function Set Metric
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery

open NoExoticSixSphere GLOrthonormalization Stiefel StabilizedSpanningDisk

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  (e : EuclideanEmbedding 7 M) (f : Sphere 3 → M)
  {b : Sphere 3} (D : DiskData b (e.toFun ∘ f))
  {T : Vector 4 → Vector ((e.ambientDimension - 7) + 5) →L[ℝ]
    Vector (e.ambientDimension + 6)}
  (A : EightDimensionalFramedProduct.FramedProduct D.toFun T) (R : EuclideanEmbedding.TubularRetraction e)
  (χ : ContDiffBump (0 : Vector 4))

def curvedDiskProduct (p : Vector 4 × Vector 4) : Vector (e.ambientDimension + 6) :=
  GeneralDiskThickening.map D.toFun A.transverse p + appendZeroMap e.ambientDimension 6
    (GeneralRadialCorrection.correction χ b (SevenSurgery.sphereTubeDifference e f A.boundaryTransverse R) p)

theorem curvedDiskProduct_core (x : Vector 4) :
    SevenSurgery.curvedDiskProduct e f D A R χ (x, 0) = D.toFun x := by
  rw [curvedDiskProduct, GeneralRadialCorrection.correction_core χ b _
    (SevenSurgery.sphereTubeDifference_core e f A.boundaryTransverse R), map_zero, add_zero,
    GeneralDiskThickening.map_core]

theorem curvedDiskProduct_eq_affine {x : Vector 4}
    (hx : x ∈ closedBall (0 : Vector 4) χ.rIn) (v : Vector 4) :
    SevenSurgery.curvedDiskProduct e f D A R χ (x, v) = GeneralDiskThickening.map D.toFun A.transverse (x, v) := by
  rw [curvedDiskProduct, GeneralRadialCorrection.correction_eq_zero χ b _ hx,
    map_zero, add_zero]

theorem curvedDiskProduct_avoids {p : Vector 4 × Vector 4}
    (hp : GeneralDiskThickening.map D.toFun A.transverse p ∉ range (appendZeroMap e.ambientDimension 6)) :
    SevenSurgery.curvedDiskProduct e f D A R χ p ∉ range (appendZeroMap e.ambientDimension 6) := by
  rintro ⟨y, hy⟩
  let w := GeneralRadialCorrection.correction χ b
    (SevenSurgery.sphereTubeDifference e f A.boundaryTransverse R) p
  apply hp
  refine ⟨y - w, ?_⟩
  rw [map_sub, hy]
  change (GeneralDiskThickening.map D.toFun A.transverse p + appendZeroMap e.ambientDimension 6 w) -
    appendZeroMap e.ambientDimension 6 w = _
  exact add_sub_cancel_right _ _

variable (hf : ContMDiff (𝓡 3) (𝓡 7) ∞ f)

include hf in
theorem contDiffAt_curvedDiskProduct {x : Vector 4} (hx : x ∈ closedBall (0 : Vector 4) 1)
    (v : Vector 4)
    (hp : (SphereRadialRetraction.retract b x, v) ∈ SevenSurgery.sphereTubeDomain e f A.boundaryTransverse R) :
    ContDiffAt ℝ ∞ (SevenSurgery.curvedDiskProduct e f D A R χ) (x, v) := by
  have hH := GeneralDiskThickening.contDiffAt_map D.toFun A.transverse x v
    D.smooth.contDiffAt (A.smooth_transverse x hx)
  have hc := GeneralRadialCorrection.contDiffAt_correction χ b
    (SevenSurgery.sphereTubeDifference e f A.boundaryTransverse R) x v
      (SevenSurgery.contMDiffAt_sphereTubeDifference e f A.boundaryTransverse R hf
        A.contMDiff_boundaryTransverse hp)
  exact hH.add ((appendZeroMap e.ambientDimension 6).contDiff.contDiffAt.comp (x, v) hc)

variable (a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel)
  (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 7) f s))
  (hTb : ∀ s : Sphere 3, T s.val = boundaryFrameOperator (SevenSurgery.normalFrameOnSphere e a f s).val)

include hf a hd hTb in
theorem fderiv_curvedDiskProduct_core {x : Vector 4} (hx : x ∈ closedBall (0 : Vector 4) 1) :
    fderiv ℝ (SevenSurgery.curvedDiskProduct e f D A R χ) (x, 0) =
      fderiv ℝ (GeneralDiskThickening.map D.toFun A.transverse) (x, 0) := by
  let g := SevenSurgery.sphereTubeDifference e f A.boundaryTransverse R
  have hgs (s : Sphere 3) : ContMDiffAt ((𝓡 3).prod (𝓡 4)) (𝓡 e.ambientDimension) ∞
      g (s, 0) := SevenSurgery.contMDiffAt_sphereTubeDifference e f A.boundaryTransverse R hf
    A.contMDiff_boundaryTransverse (SevenSurgery.core_mem_sphereTubeDomain e f A.boundaryTransverse R s)
  have hgj (s : Sphere 3) : mfderiv ((𝓡 3).prod (𝓡 4)) (𝓡 e.ambientDimension) g (s, 0) = 0 :=
    SevenSurgery.mfderiv_sphereTubeDifference_core e f A.boundaryTransverse R hf A.contMDiff_boundaryTransverse
      hd (fun s ↦ Stiefel.injective
        ⟨A.boundaryTransverse s, SevenSurgery.norm_boundaryTransverse e a f hf hd D A hTb s⟩)
      (SevenSurgery.range_boundaryTransverse e a f hf hd D A hTb) s
  have hc := (GeneralRadialCorrection.contDiffAt_correction χ b g x 0
    (hgs (SphereRadialRetraction.retract b x))).differentiableAt (by simp)
  have hj := GeneralRadialCorrection.fderiv_correction_core χ b g hgs
    (SevenSurgery.sphereTubeDifference_core e f A.boundaryTransverse R) hgj x
  have hc' := hc.hasFDerivAt
  rw [hj] at hc'
  have hH := (GeneralDiskThickening.contDiffAt_map D.toFun A.transverse x 0
    D.smooth.contDiffAt (A.smooth_transverse x hx)).differentiableAt (by simp)
  have he := (hH.hasFDerivAt.add
    ((appendZeroMap e.ambientDimension 6).hasFDerivAt.comp (x, 0) hc')).fderiv
  change fderiv ℝ (SevenSurgery.curvedDiskProduct e f D A R χ) (x, 0) = _ at he
  simpa only [ContinuousLinearMap.comp_zero, add_zero] using he

end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery

noncomputable section

open Function
open scoped Manifold ContDiff
open Wikipedia.SmoothSixDPoincare.SphereBoundary

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
  (A : EightDimensionalFramedProduct.FramedProduct D.toFun T) (R : EuclideanEmbedding.TubularRetraction e)
  (χ : ContDiffBump (0 : Vector 4))
  (hTb : ∀ s : Sphere 3, T s.val = boundaryFrameOperator (SevenSurgery.normalFrameOnSphere e a f s).val)

include a hf hd hTb in
theorem curvedDiskProduct_collar {x : Vector 4} (hx : (1 / 2 : ℝ) < ‖x‖)
    (hχ : χ.rOut ≤ ‖x‖) (hDx : D.toFun x = collar b (e.toFun ∘ f) x)
    (hCx : A.transverse x = A.transverse (SphereRadialRetraction.retract b x).val)
    (v : Vector 4) :
    SevenSurgery.curvedDiskProduct e f D A R χ (x, v) = coordinates e.ambientDimension 4
      ((e.toFun (SevenSurgery.internalSphereTube e f A.boundaryTransverse R
        (SphereRadialRetraction.retract b x, v)), definingFunction x), 0) := by
  rw [curvedDiskProduct, SevenSurgery.thickening_radial_collar e a f hf hd D A hTb hx hDx hCx,
    GeneralRadialCorrection.correction_eq_radial χ b _ hχ,
    ← coordinates_old e.ambientDimension 4, ← map_add]
  simp only [Prod.mk_add_mk, add_zero]
  rw [SevenSurgery.ambientSphereTube_add_difference e]

include a hf hd hTb in
theorem curvedDiskProduct_boundary (hχ : χ.rOut ≤ 1) (s : Sphere 3) (v : Vector 4) :
    SevenSurgery.curvedDiskProduct e f D A R χ (s.val, v) = appendZeroMap e.ambientDimension 6
      (e.toFun (SevenSurgery.internalSphereTube e f A.boundaryTransverse R (s, v))) := by
  have hχs : χ.rOut ≤ ‖s.val‖ := by rw [ClosedHemisphere.unit_norm]; exact hχ
  rw [curvedDiskProduct, SevenSurgery.thickening_boundary_affine e a f hf hd D A hTb,
    GeneralRadialCorrection.correction_eq_radial χ b _ hχs,
    SphereRadialRetraction.retract_coe, ← map_add, SevenSurgery.ambientSphereTube_add_difference e]

end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery
