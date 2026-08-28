import Wikipedia.HopfProblem.ConstantSheafSingularComparisonPushforwardExtAugmented
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonPushforwardExtCycles
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonPushforwardExtComposition
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonPushforwardExtTruncationTwo

/-!
# The actual degree-two truncated pushforward comparison
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison.PushforwardExt

open CuspNormalization.SheafCohomologyResolution
open CuspNormalization.SheafCohomologyFinitePushforward
open LowExt

variable {X Y : TopCat.{0}} [T2Space X] (f : X ⟶ Y)
  (hf : IsClosedMap f) (hfinite : ∀ y : Y, (f ⁻¹' {y}).Finite)
  (R : CochainResolution (AbelianSheaf X))

/-- Compose the actual augmented pushforward square, native
truncation square and global-cycle square in degree two. -/
theorem h2_forward_composite
    [Subsingleton (CategoryTheory.Sheaf.H.{0} R.truncation.complex.X₁ 1)]
    [Subsingleton (CategoryTheory.Sheaf.H.{0} R.truncation.complex.X₁ 2)]
    [Subsingleton (CategoryTheory.Sheaf.H.{0} R.truncation.complex.X₂ 1)]
    [Subsingleton (CategoryTheory.Sheaf.H.{0}
      (pushforwardResolution f hf hfinite R).truncation.complex.X₁ 1)]
    [Subsingleton (CategoryTheory.Sheaf.H.{0}
      (pushforwardResolution f hf hfinite R).truncation.complex.X₁ 2)]
    [Subsingleton (CategoryTheory.Sheaf.H.{0}
      (pushforwardResolution f hf hfinite R).truncation.complex.X₂ 1)] :
    forwardHom f hf hfinite R.F 2 ≫
        ((pushforwardResolution f hf hfinite R).truncation.h2Iso.hom ≫
          (pushforwardResolution f hf hfinite R).globalSecondHomologyIso.hom) =
      R.truncation.h2Iso.hom ≫ R.globalSecondHomologyIso.hom := by
  let S := pushforwardResolution f hf hfinite R
  let M := pushforwardAugmentedResolution f hf hfinite R.truncation
  let φ := pushforwardTruncationMap f hf hfinite R
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} M.complex.X₁ 1) :=
    ‹Subsingleton (CategoryTheory.Sheaf.H.{0}
      (pushforwardResolution f hf hfinite R).truncation.complex.X₁ 1)›
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} M.complex.X₁ 2) :=
    ‹Subsingleton (CategoryTheory.Sheaf.H.{0}
      (pushforwardResolution f hf hfinite R).truncation.complex.X₁ 2)›
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} M.complex.X₂ 1) :=
    ‹Subsingleton (CategoryTheory.Sheaf.H.{0}
      (pushforwardResolution f hf hfinite R).truncation.complex.X₂ 1)›
  exact comparison_of_truncation
    (forwardHom f hf hfinite R.F 2) R.truncation.h2Iso.hom R.globalSecondHomologyIso.hom
    M.h2Iso.hom S.truncation.h2Iso.hom S.globalSecondHomologyIso.hom φ.globalCokernelMap
    (augmented_h2_forward f hf hfinite R.truncation) (truncation_h2Iso_hom f hf hfinite R)
    (pushforwardTruncationMap_globalSecondHomology f hf hfinite R)

end Wikipedia.HopfProblem.ConstantSheafSingularComparison.PushforwardExt
