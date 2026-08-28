import Wikipedia.HopfProblem.TrianglePeriodFamilyFundamentalGroupFreeInversion
import Wikipedia.HopfProblem.TriangleRiemannNormalization

/-!
# The two meridians with the orientation of the actual half-triangle

The actual half-triangle normalization may take its values in either
half-plane. We choose the semicircles on its side of the real axis and
their conjugates. The resulting two full loops are either both positive
meridians or both of their inverses. Thus they are an actual free basis,
without any assumption about the normalization's orientation.
-/

noncomputable section

open Set Complex
open scoped Topology ComplexConjugate

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Meridians

open SpecialPeriods.Triangle RiemannMapping FreeMeridianMarking

/-- Whether the actual half-triangle occupies the upper half-plane. -/
def normalizationReversesMeridians : Bool := decide (0 < normalizationOrientation)

private theorem halfCircle_im_nonneg (t : unitInterval) :
    0 ≤ (meridianHalfCircle t).im := by
  rw [meridianHalfCircle, circleMap_zero_im]
  apply mul_nonneg (by norm_num)
  exact Real.sin_nonneg_of_nonneg_of_le_pi
    (mul_nonneg Real.pi_pos.le t.property.1)
    (by nlinarith [Real.pi_pos, t.property.2])

theorem upperZeroPath_im_nonneg (t : unitInterval) :
    0 ≤ (upperZeroPath t : ℂ).im := halfCircle_im_nonneg t

theorem lowerZeroPath_im_nonpos (t : unitInterval) :
    (lowerZeroPath t : ℂ).im ≤ 0 := by
  change (conj (meridianHalfCircle t)).im ≤ 0
  simpa using halfCircle_im_nonneg t

theorem upperOnePath_im_nonneg (t : unitInterval) :
    0 ≤ (upperOnePath t : ℂ).im := by
  change 0 ≤ (1 - conj (meridianHalfCircle t)).im
  simpa using halfCircle_im_nonneg t

theorem lowerOnePath_im_nonpos (t : unitInterval) :
    (lowerOnePath t : ℂ).im ≤ 0 := by
  change (1 - meridianHalfCircle t).im ≤ 0
  simpa using halfCircle_im_nonneg t

/-- The zero semicircle on the side occupied by the actual normalization. -/
def zeroHalfPath : Path meridianBasepoint meridianLeftPoint :=
  if 0 < normalizationOrientation then upperZeroPath else lowerZeroPath

/-- The one semicircle on the side occupied by the actual normalization. -/
def oneHalfPath : Path meridianBasepoint meridianRightPoint :=
  if 0 < normalizationOrientation then upperOnePath else lowerOnePath

/-- The zero semicircle on the opposite side. -/
def oppositeZeroPath : Path meridianBasepoint meridianLeftPoint :=
  if 0 < normalizationOrientation then lowerZeroPath else upperZeroPath

/-- The one semicircle on the opposite side. -/
def oppositeOnePath : Path meridianBasepoint meridianRightPoint :=
  if 0 < normalizationOrientation then lowerOnePath else upperOnePath

theorem zeroHalfPath_mem_halfPlane (t : unitInterval) :
    0 ≤ normalizationOrientation * (zeroHalfPath t : ℂ).im := by
  by_cases ho : 0 < normalizationOrientation
  · rw [zeroHalfPath, if_pos ho]
    exact mul_nonneg ho.le (upperZeroPath_im_nonneg t)
  · rw [zeroHalfPath, if_neg ho]
    exact mul_nonneg_of_nonpos_of_nonpos (le_of_not_gt ho) (lowerZeroPath_im_nonpos t)

theorem oneHalfPath_mem_halfPlane (t : unitInterval) :
    0 ≤ normalizationOrientation * (oneHalfPath t : ℂ).im := by
  by_cases ho : 0 < normalizationOrientation
  · rw [oneHalfPath, if_pos ho]
    exact mul_nonneg ho.le (upperOnePath_im_nonneg t)
  · rw [oneHalfPath, if_neg ho]
    exact mul_nonneg_of_nonpos_of_nonpos (le_of_not_gt ho) (lowerOnePath_im_nonpos t)

theorem oppositeZeroPath_coe (t : unitInterval) :
    (oppositeZeroPath t : ℂ) = conj (zeroHalfPath t : ℂ) := by
  by_cases ho : 0 < normalizationOrientation
  · rw [oppositeZeroPath, zeroHalfPath, if_pos ho, if_pos ho]
    rfl
  · rw [oppositeZeroPath, zeroHalfPath, if_neg ho, if_neg ho]
    exact (conj_conj (meridianHalfCircle t)).symm

theorem oppositeOnePath_coe (t : unitInterval) :
    (oppositeOnePath t : ℂ) = conj (oneHalfPath t : ℂ) := by
  by_cases ho : 0 < normalizationOrientation
  · rw [oppositeOnePath, oneHalfPath, if_pos ho, if_pos ho]
    change 1 - meridianHalfCircle t = conj (1 - conj (meridianHalfCircle t))
    simp only [map_sub, map_one, conj_conj]
  · rw [oppositeOnePath, oneHalfPath, if_neg ho, if_neg ho]
    change 1 - conj (meridianHalfCircle t) = conj (1 - meridianHalfCircle t)
    simp only [map_sub, map_one]

/-- The explicit loops whose lifts will have the source's inverse-generator
endpoints. Their freeness is already settled independently of that lift. -/
def compatiblePlanarMeridian (b : Bool) : Path meridianBasepoint meridianBasepoint :=
  if b then oneHalfPath.trans oppositeOnePath.symm
  else oppositeZeroPath.trans zeroHalfPath.symm

theorem compatiblePlanarMeridian_eq (b : Bool) :
    compatiblePlanarMeridian b =
      if 0 < normalizationOrientation then
        (if b then positiveMeridianOne else positiveMeridianZero).symm
      else if b then positiveMeridianOne else positiveMeridianZero := by
  cases b <;> by_cases ho : 0 < normalizationOrientation <;>
    simp [compatiblePlanarMeridian, zeroHalfPath, oneHalfPath, oppositeZeroPath,
      oppositeOnePath, ho, positiveMeridianZero, positiveMeridianOne,
      Path.trans_symm, Path.symm_symm]

theorem compatiblePlanarMeridian_class (b : Bool) :
    FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (compatiblePlanarMeridian b)) =
      orientedClass normalizationReversesMeridians b := by
  rw [compatiblePlanarMeridian_eq]
  by_cases ho : 0 < normalizationOrientation
  · simp only [if_pos ho, orientedClass, normalizationReversesMeridians,
      decide_eq_true_eq.mpr ho, ↓reduceIte]
    rfl
  · simp only [if_neg ho, orientedClass, normalizationReversesMeridians,
      decide_eq_false_iff_not.mpr ho, Bool.false_eq_true, ↓reduceIte]
    rfl

/-- Both selected loops are a proved free basis of the actual planar group. -/
theorem compatiblePlanarMeridian_free (b : Bool) :
    orientedEquiv normalizationReversesMeridians
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (compatiblePlanarMeridian b))) =
        FreeGroup.of b := by
  rw [compatiblePlanarMeridian_class, orientedEquiv_orientedClass]

end Wikipedia.HopfProblem.TrianglePeriodFamily.Meridians
