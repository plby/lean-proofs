import Wikipedia.NoExoticSixSphere.SphereTubeDifference
import Wikipedia.NoExoticSixSphere.RadialCollarCorrectionJet
import Wikipedia.NoExoticSixSphere.FramedDiskRadialCollar

/-!
# The actual curved-face correction of the disk product

Add the supported radial curved-minus-affine difference in the old ambient
coordinates only. This fixes the disk core, is smooth on the actual tube
domain, and preserves avoidance of the old ambient space. Its core derivative
is unchanged when the original transverse frame has the proved normal range.
-/

noncomputable section

open Function Set Metric
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization Stiefel StabilizedSpanningDisk

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (e : EuclideanEmbedding 6 M) (f : Sphere 3 → M)
  {b : Sphere 3} (D : DiskData b (e.toFun ∘ f))
  {T : Vector 4 → Vector ((e.ambientDimension - 6) + 5) →L[ℝ]
    Vector (e.ambientDimension + 6)}
  (A : DiskThickening.FramedProduct D.toFun T) (R : TubularRetraction e)
  (χ : ContDiffBump (0 : Vector 4))

def curvedDiskProduct (p : Vector 4 × Vector 3) : Vector (e.ambientDimension + 6) :=
  DiskThickening.map D.toFun A.transverse p + appendZeroMap e.ambientDimension 6
    (RadialCollarCorrection.correction χ b (e.sphereTubeDifference f A.boundaryTransverse R) p)

theorem curvedDiskProduct_core (x : Vector 4) :
    e.curvedDiskProduct f D A R χ (x, 0) = D.toFun x := by
  rw [curvedDiskProduct, RadialCollarCorrection.correction_core χ b _
    (e.sphereTubeDifference_core f A.boundaryTransverse R), map_zero, add_zero,
    DiskThickening.map_core]

theorem curvedDiskProduct_eq_affine {x : Vector 4}
    (hx : x ∈ closedBall (0 : Vector 4) χ.rIn) (v : Vector 3) :
    e.curvedDiskProduct f D A R χ (x, v) = DiskThickening.map D.toFun A.transverse (x, v) := by
  rw [curvedDiskProduct, RadialCollarCorrection.correction_eq_zero χ b _ hx,
    map_zero, add_zero]

theorem curvedDiskProduct_avoids {p : Vector 4 × Vector 3}
    (hp : DiskThickening.map D.toFun A.transverse p ∉ range (appendZeroMap e.ambientDimension 6)) :
    e.curvedDiskProduct f D A R χ p ∉ range (appendZeroMap e.ambientDimension 6) := by
  rintro ⟨y, hy⟩
  let w := RadialCollarCorrection.correction χ b
    (e.sphereTubeDifference f A.boundaryTransverse R) p
  apply hp
  refine ⟨y - w, ?_⟩
  rw [map_sub, hy]
  change (DiskThickening.map D.toFun A.transverse p + appendZeroMap e.ambientDimension 6 w) -
    appendZeroMap e.ambientDimension 6 w = _
  exact add_sub_cancel_right _ _

variable (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f)

include hf in
theorem contDiffAt_curvedDiskProduct {x : Vector 4} (hx : x ∈ closedBall (0 : Vector 4) 1)
    (v : Vector 3)
    (hp : (SphereRadialRetraction.retract b x, v) ∈ e.sphereTubeDomain f A.boundaryTransverse R) :
    ContDiffAt ℝ ∞ (e.curvedDiskProduct f D A R χ) (x, v) := by
  have hH := DiskThickening.contDiffAt_map D.toFun A.transverse x v
    D.smooth.contDiffAt (A.smooth_transverse x hx)
  have hc := RadialCollarCorrection.contDiffAt_correction χ b
    (e.sphereTubeDifference f A.boundaryTransverse R) x v
      (e.contMDiffAt_sphereTubeDifference f A.boundaryTransverse R hf
        A.contMDiff_boundaryTransverse hp)
  exact hH.add ((appendZeroMap e.ambientDimension 6).contDiff.contDiffAt.comp (x, v) hc)

variable (a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)
  (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s))
  (hTb : ∀ s : Sphere 3, T s.val = boundaryFrameOperator (e.normalFrameOnSphere a f s).val)

include hf a hd hTb in
theorem fderiv_curvedDiskProduct_core {x : Vector 4} (hx : x ∈ closedBall (0 : Vector 4) 1) :
    fderiv ℝ (e.curvedDiskProduct f D A R χ) (x, 0) =
      fderiv ℝ (DiskThickening.map D.toFun A.transverse) (x, 0) := by
  let g := e.sphereTubeDifference f A.boundaryTransverse R
  have hgs (s : Sphere 3) : ContMDiffAt ((𝓡 3).prod (𝓡 3)) (𝓡 e.ambientDimension) ∞
      g (s, 0) := e.contMDiffAt_sphereTubeDifference f A.boundaryTransverse R hf
    A.contMDiff_boundaryTransverse (e.core_mem_sphereTubeDomain f A.boundaryTransverse R s)
  have hgj (s : Sphere 3) : mfderiv ((𝓡 3).prod (𝓡 3)) (𝓡 e.ambientDimension) g (s, 0) = 0 :=
    e.mfderiv_sphereTubeDifference_core f A.boundaryTransverse R hf A.contMDiff_boundaryTransverse
      hd (fun s ↦ Stiefel.injective
        ⟨A.boundaryTransverse s, e.norm_boundaryTransverse a f hf hd D A hTb s⟩)
      (e.range_boundaryTransverse a f hf hd D A hTb) s
  have hc := (RadialCollarCorrection.contDiffAt_correction χ b g x 0
    (hgs (SphereRadialRetraction.retract b x))).differentiableAt (by simp)
  have hj := RadialCollarCorrection.fderiv_correction_core χ b g hgs
    (e.sphereTubeDifference_core f A.boundaryTransverse R) hgj x
  have hc' := hc.hasFDerivAt
  rw [hj] at hc'
  have hH := (DiskThickening.contDiffAt_map D.toFun A.transverse x 0
    D.smooth.contDiffAt (A.smooth_transverse x hx)).differentiableAt (by simp)
  have he := (hH.hasFDerivAt.add
    ((appendZeroMap e.ambientDimension 6).hasFDerivAt.comp (x, 0) hc')).fderiv
  change fderiv ℝ (e.curvedDiskProduct f D A R χ) (x, 0) = _ at he
  simpa only [ContinuousLinearMap.comp_zero, add_zero] using he

end NoExoticSixSphere.EuclideanEmbedding
