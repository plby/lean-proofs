import Wikipedia.HopfProblem.ConstantSheafSingularComparisonPushforwardExtTruncation

/-!
# Native degree-two naturality for the actual truncation morphism
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

/-- The actual augmentation of the truncation comparison is identity,
so its native degree-two naturality square has identity on cohomology. -/
theorem truncation_h2Iso_hom
    [Subsingleton (CategoryTheory.Sheaf.H.{0}
      (pushforwardAugmentedResolution f hf hfinite R.truncation).complex.X₁ 1)]
    [Subsingleton (CategoryTheory.Sheaf.H.{0}
      (pushforwardAugmentedResolution f hf hfinite R.truncation).complex.X₁ 2)]
    [Subsingleton (CategoryTheory.Sheaf.H.{0}
      (pushforwardAugmentedResolution f hf hfinite R.truncation).complex.X₂ 1)]
    [Subsingleton (CategoryTheory.Sheaf.H.{0}
      (pushforwardResolution f hf hfinite R).truncation.complex.X₁ 1)]
    [Subsingleton (CategoryTheory.Sheaf.H.{0}
      (pushforwardResolution f hf hfinite R).truncation.complex.X₁ 2)]
    [Subsingleton (CategoryTheory.Sheaf.H.{0}
      (pushforwardResolution f hf hfinite R).truncation.complex.X₂ 1)] :
    (pushforwardResolution f hf hfinite R).truncation.h2Iso.hom =
      (pushforwardAugmentedResolution f hf hfinite R.truncation).h2Iso.hom ≫
        (pushforwardTruncationMap f hf hfinite R).globalCokernelMap := by
  let S := pushforwardResolution f hf hfinite R
  let φ := pushforwardTruncationMap f hf hfinite R
  have hn := φ.h2Iso_naturality
  have haug : φ.augmentation = 𝟙 ((pushforward f).obj R.F) := rfl
  have hid : (CategoryTheory.Sheaf.functorH _ 2).map φ.augmentation =
      𝟙 (AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0} ((pushforward f).obj R.F) 2)) :=
    (congrArg (CategoryTheory.Sheaf.functorH _ 2).map haug).trans
      ((CategoryTheory.Sheaf.functorH _ 2).map_id _)
  exact (Category.id_comp _).symm.trans
    ((congrArg (fun k => k ≫ S.truncation.h2Iso.hom) hid.symm).trans hn)

end Wikipedia.HopfProblem.ConstantSheafSingularComparison.PushforwardExt
