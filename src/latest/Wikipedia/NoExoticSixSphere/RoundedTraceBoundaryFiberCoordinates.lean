import Wikipedia.NoExoticSixSphere.RoundedTraceBoundaryFrameNormalization
import Wikipedia.NoExoticSixSphere.LastCoordinateScale

/-!
# Explicit fiber coordinates for the signed boundary-frame normalization

Divide the interpolated last-column scale by the original nonzero scale.
The resulting positive rescaling is the identity initially and changes the
actual original frame to its checked signed unit frame at the final time.
-/

noncomputable section

open Function Set
open scoped Manifold ContDiff unitInterval

namespace NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace

open GLOrthonormalization Stiefel

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M] [CompactSpace M]
  [IsManifold (𝓡 6) ∞ M] {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

def boundaryFrameRatio (q : I × Boundary A) : ℝ :=
  boundaryFrameScale A q.1 q.2 / boundaryVerticalScale A q.2

theorem boundaryFrameRatio_pos (q : I × Boundary A) : 0 < boundaryFrameRatio A q := by
  rcases (boundary_iff_mem_ends A q.2.val).mp q.2.property with hp | hp
  · exact div_pos (boundaryFrameScale_pos_other A q.1 q.2 hp)
      (boundaryVerticalScale_pos_other A q.2 hp)
  · exact div_pos_of_neg_of_neg (boundaryFrameScale_neg_top A q.1 q.2 hp)
      (boundaryVerticalScale_neg_top A q.2 hp)

theorem continuous_boundaryFrameRatio : Continuous (boundaryFrameRatio A) := by
  let := boundaryChartedSpace A
  have ht : Continuous (fun q : I × Boundary A ↦ ((q.1 : ℝ), q.2)) :=
    (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  exact (((contMDiff_boundaryFrameScale A).continuous).comp ht).div
    ((contMDiff_boundaryVerticalScale A).continuous.comp continuous_snd)
      (fun q ↦ boundaryVerticalScale_ne_zero A q.2)

theorem boundaryFrameRatio_zero (p : Boundary A) : boundaryFrameRatio A (0, p) = 1 := by
  change ((1 - 0) * boundaryVerticalScale A p + 0 * boundaryUnitScale A p) /
    boundaryVerticalScale A p = 1
  rw [sub_zero, one_mul, zero_mul, add_zero, div_self (boundaryVerticalScale_ne_zero A p)]

def boundaryFiberCoordinates (q : I × Boundary A) :
    TimeGraphFrameSpace (e := e) ≃L[ℝ] TimeGraphFrameSpace (e := e) :=
  lastCoordinateScale (boundaryFrameRatio A q) (ne_of_gt (boundaryFrameRatio_pos A q))

theorem boundaryFiberCoordinates_zero (p : Boundary A) :
    boundaryFiberCoordinates A (0, p) = ContinuousLinearEquiv.refl ℝ _ := by
  apply ContinuousLinearEquiv.ext
  funext v
  apply (WithLp.prodContinuousLinearEquiv 2 ℝ (Vector ((e.ambientDimension - 6) + 5)) ℝ).injective
  change (v.fst, v.snd * boundaryFrameRatio A (0, p)) = (v.fst, v.snd)
  rw [boundaryFrameRatio_zero, mul_one]

theorem continuous_boundaryFiberCoordinates :
    Continuous (fun q : (I × Boundary A) × TimeGraphFrameSpace (e := e) ↦
      boundaryFiberCoordinates A q.1 q.2) :=
  continuous_lastCoordinateScale_apply (continuous_boundaryFrameRatio A)
    (fun q ↦ ne_of_gt (boundaryFrameRatio_pos A q))

theorem continuous_boundaryFiberCoordinates_symm :
    Continuous (fun q : (I × Boundary A) × TimeGraphFrameSpace (e := e) ↦
      (boundaryFiberCoordinates A q.1).symm q.2) :=
  continuous_lastCoordinateScale_symm_apply (continuous_boundaryFrameRatio A)
    (fun q ↦ ne_of_gt (boundaryFrameRatio_pos A q))

theorem boundaryVerticalFrame_fiberCoordinates (t : I) (p : Boundary A)
    (v : TimeGraphFrameSpace (e := e)) :
    boundaryVerticalFrame A p (boundaryFiberCoordinates A (t, p) v) =
      boundaryFrameHomotopy A (t, p) v := by
  rw [boundaryVerticalFrame_eq_operator]
  change traceNormalFrame A p.val v.fst +
    (v.snd * (boundaryFrameScale A t p / boundaryVerticalScale A p)) •
      (boundaryVerticalScale A p • outwardNormal A p) =
    traceNormalFrame A p.val v.fst + v.snd • (boundaryFrameScale A t p • outwardNormal A p)
  rw [smul_smul, smul_smul, mul_assoc,
    div_mul_cancel₀ _ (boundaryVerticalScale_ne_zero A p)]

end NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace
