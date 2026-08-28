import Wikipedia.HopfProblem.ConstantSheafSingularComparisonOriginalConstants
import Wikipedia.HopfProblem.CuspNormalizationSheafConstantsCuspTerms

/-!
# Identification of the original normalization constant map

The native constant-sheaf pullback along the genuine normalization map
agrees with the literal first arrow of the original constant-sheaf
normalization sequence, under the original additive comparisons.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison.OriginalConstants

open CuspNormalization

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)

/-- The actual constant normalization arrow is the native pullback
along the original geometric normalization map after comparison. -/
@[reassoc]
theorem normalizationConstantPullback_complexAdditiveSheafIso :
    SheafResolution.normalizationConstantPullback C ε hε ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat
          (SheafResolution.normalizationMap C ε hε)).map
            (SheafConstants.complexAdditiveSheafIso
              (TopCat.of (ToricSpace.rayDivisor 0))).hom =
      (SheafConstants.complexAdditiveSheafIso
        (TopCat.of (SheafResolution.CentralSpace C ε))).hom ≫
          PullbackSheaf.constantPullback (SheafResolution.normalizationMap C ε hε)
            (AddCommGrpCat.of ℂ) :=
  additivePullbackMap_complexAdditiveSheafIso (SheafResolution.normalizationMap C ε hε)

/-- Direct equality with the original normalization constant map;
no replacement of the geometric arrow or of the sheaf comparison occurs. -/
theorem normalizationConstantPullback_eq :
    SheafResolution.normalizationConstantPullback C ε hε =
      (SheafConstants.complexAdditiveSheafIso
        (TopCat.of (SheafResolution.CentralSpace C ε))).hom ≫
          PullbackSheaf.constantPullback (SheafResolution.normalizationMap C ε hε)
            (AddCommGrpCat.of ℂ) ≫
              (TopCat.Sheaf.pushforward AddCommGrpCat
                (SheafResolution.normalizationMap C ε hε)).map
                  (SheafConstants.complexAdditiveSheafIso
                    (TopCat.of (ToricSpace.rayDivisor 0))).inv :=
  additivePullbackMap_eq (SheafResolution.normalizationMap C ε hε)

end Wikipedia.HopfProblem.ConstantSheafSingularComparison.OriginalConstants
