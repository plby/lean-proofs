import Wikipedia.NoExoticSixSphere.SmoothOperatorComplement

/-!
# The actual normal projection for a product map

Before using the Gram formula, put the derivative's source in Euclidean
coordinates of the same dimension. The plain product norm is not an inner-product
norm. This coordinate equivalence preserves the actual derivative range.
-/

noncomputable section

open Function
open scoped ContDiff

namespace NoExoticSixSphere.DiskThickening

open GLOrthonormalization Stiefel

variable {N d : ℕ} (H : Vector 4 × Vector d → Vector N)

def productDerivative (p : Vector 4 × Vector d) : Vector (4 + d) →L[ℝ] Vector N :=
  (fderiv ℝ H p).comp
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 4) (m := d)).toContinuousLinearMap

theorem range_productDerivative (p : Vector 4 × Vector d) :
    (productDerivative H p).range = (fderiv ℝ H p).range := by
  change LinearMap.range ((fderiv ℝ H p).toLinearMap.comp
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 4) (m := d)).toLinearEquiv.toLinearMap) = _
  rw [LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _)]

theorem injective_productDerivative (p : Vector 4 × Vector d)
    (hi : Injective (fderiv ℝ H p)) : Injective (productDerivative H p) :=
  hi.comp (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 4) (m := d)).injective

def productNormalProjection : Vector 4 × Vector d → Vector N →L[ℝ] Vector N :=
  OperatorComplement.projection (productDerivative H)

theorem range_productNormalProjection (p : Vector 4 × Vector d)
    (hi : Injective (fderiv ℝ H p)) :
    (productNormalProjection H p).range = (fderiv ℝ H p).rangeᗮ := by
  rw [productNormalProjection, OperatorComplement.range_projection _ _
    (injective_productDerivative H p hi), range_productDerivative]

theorem idempotent_productNormalProjection (p : Vector 4 × Vector d)
    (hi : Injective (fderiv ℝ H p)) : IsIdempotentElem (productNormalProjection H p) :=
  OperatorComplement.idempotent_projection _ _ (injective_productDerivative H p hi)

theorem contDiffAt_productNormalProjection (p : Vector 4 × Vector d)
    (hs : ContDiffAt ℝ ∞ H p) (hi : Injective (fderiv ℝ H p)) :
    ContDiffAt ℝ ∞ (productNormalProjection H) p :=
  OperatorComplement.contDiffAt_projection _ _
    ((hs.fderiv_right (by simp)).clm_comp contDiffAt_const)
    (injective_productDerivative H p hi)

end NoExoticSixSphere.DiskThickening
