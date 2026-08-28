import Wikipedia.NoExoticSixSphere.StereographicAugmentedDifferential
import Wikipedia.NoExoticSixSphere.PartialFrameBlockSum

/-!
# Fixed normal coordinates for the compactified frame

The full equation operator uses twice the new radial coordinate and
the inverse tube radius on the original normal coordinates. This fixed
linear equivalence identifies its normal frame with the ordinary
one-column stabilization under the actual variable ambient coordinates.
-/

noncomputable section

namespace NoExoticSixSphere.StereographicEquator

open Stiefel GLOrthonormalization

theorem augmentedCoordinates_appendZero (n : ℕ) (x v : V n) :
    augmentedCoordinates n x (appendZeroMap n 1 v) = fderiv ℝ (finiteAmbient n) x v := by
  rw [augmentedCoordinates_apply, EuclideanTailCoordinates.split_apply]
  change fderiv ℝ (finiteAmbient n) x
    (EuclideanSpace.finAddEquivProd
      (EuclideanSpace.finAddEquivProd.symm (v, (0 : V 1)))).1 +
    EuclideanTailCoordinates.scalar.symm (EuclideanSpace.finAddEquivProd
      (EuclideanSpace.finAddEquivProd.symm (v, (0 : V 1)))).2 • finiteAmbient n x = _
  rw [ContinuousLinearEquiv.apply_symm_apply]
  simp only [map_zero, zero_smul, add_zero]

theorem augmentedCoordinates_block {n q : ℕ} (x : V n) (A : V q →L[ℝ] V n)
    (v : V (q + 1)) :
    augmentedCoordinates n x (BlockSum.operator 1 A v) =
      augmentedEquiv n x
        (A (EuclideanTailCoordinates.split q v).snd, (EuclideanTailCoordinates.split q v).fst) := by
  rw [augmentedCoordinates_apply, EuclideanTailCoordinates.split_apply, BlockSum.operator_apply,
    ContinuousLinearEquiv.apply_symm_apply, augmentedEquiv_apply]
  rfl

def normalEquationCoordinates (q : ℕ) (r : ℝ) (hr : r ≠ 0) :
    V (q + 1) ≃L[ℝ] WithLp 2 (ℝ × V q) :=
  (EuclideanTailCoordinates.split q).toContinuousLinearEquiv.trans
    ((WithLp.prodContinuousLinearEquiv 2 ℝ ℝ (V q)).trans
      ((((LinearEquiv.smulOfNeZero ℝ ℝ (2 : ℝ) (by norm_num)).toContinuousLinearEquiv).prodCongr
        (LinearEquiv.smulOfNeZero ℝ (V q) r⁻¹ (inv_ne_zero hr)).toContinuousLinearEquiv).trans
          (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ (V q)).symm))

theorem normalEquationCoordinates_apply (q : ℕ) (r : ℝ) (hr : r ≠ 0) (v : V (q + 1)) :
    normalEquationCoordinates q r hr v = WithLp.toLp 2
      (2 * (EuclideanTailCoordinates.split q v).fst,
        r⁻¹ • (EuclideanTailCoordinates.split q v).snd) := rfl

theorem normalFrame_block {n q : ℕ} (x : V n) (A : V q →L[ℝ] V n)
    (r : ℝ) (hr : r ≠ 0) (R : WithLp 2 (ℝ × V q) →L[ℝ] V (n + 1))
    (hR : ∀ t z, R (WithLp.toLp 2 (t, z)) = augmentedEquiv n x (r • A z, t / 2))
    (v : V (q + 1)) :
    R (normalEquationCoordinates q r hr v) =
      augmentedCoordinates n x (BlockSum.operator 1 A v) := by
  rw [normalEquationCoordinates_apply, hR, augmentedCoordinates_block]
  congr 1
  apply Prod.ext
  · simp only [map_smul, smul_smul, mul_inv_cancel₀ hr, one_smul]
  · change (2 * (EuclideanTailCoordinates.split q v).fst) / 2 =
      (EuclideanTailCoordinates.split q v).fst
    ring

end NoExoticSixSphere.StereographicEquator
