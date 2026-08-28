import Wikipedia.HopfProblem.ConstantSheafSingularComparisonPushforwardExtAugmentedOne
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonPushforwardExtGlobalOne
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonPushforwardExtComposition

/-!
# Native degree-one cochain-resolution comparison under finite pushforward
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

/-- The original canonical `LowExt` degree-one comparison commutes
with the native finite-pushforward cohomology map. -/
theorem h1_forward_native
    [Subsingleton (CategoryTheory.Sheaf.H.{0} (R.K.X 0) 1)]
    [Subsingleton (CategoryTheory.Sheaf.H.{0}
      ((pushforwardResolution f hf hfinite R).K.X 0) 1)] :
    forwardHom f hf hfinite R.F 1 ≫
        (pushforwardResolution f hf hfinite R).h1Iso.hom = R.h1Iso.hom := by
  let S := pushforwardResolution f hf hfinite R
  let M := pushforwardAugmentedResolution f hf hfinite R.truncation
  let φ := pushforwardTruncationMap f hf hfinite R
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} R.truncation.complex.X₁ 1) :=
    ‹Subsingleton (CategoryTheory.Sheaf.H.{0} (R.K.X 0) 1)›
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} M.complex.X₁ 1) :=
    ‹Subsingleton (CategoryTheory.Sheaf.H.{0}
      ((pushforwardResolution f hf hfinite R).K.X 0) 1)›
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} S.truncation.complex.X₁ 1) :=
    ‹Subsingleton (CategoryTheory.Sheaf.H.{0}
      ((pushforwardResolution f hf hfinite R).K.X 0) 1)›
  have hnat : S.truncation.h1Iso.hom =
      M.h1Iso.hom ≫ ShortComplex.homologyMap φ.globalMap :=
    remove_functor_map_id (CategoryTheory.Sheaf.functorH _ 1) ((pushforward f).obj R.F)
      φ.h1Iso_naturality
  exact comparison_of_truncation
    (forwardHom f hf hfinite R.F 1) R.truncation.h1Iso.hom R.globalFirstHomologyIso.hom
    M.h1Iso.hom S.truncation.h1Iso.hom S.globalFirstHomologyIso.hom
    (ShortComplex.homologyMap φ.globalMap)
    (augmented_h1_forward f hf hfinite R.truncation) hnat
    (globalFirstHomology_truncation f hf hfinite R)

/-- The very same canonical degree-one isomorphism for the pushed
resolution; its acyclicity is proved by native finite-pushforward cohomology. -/
def pushedH1Iso [Subsingleton (CategoryTheory.Sheaf.H.{0} (R.K.X 0) 1)] :
    AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0} ((pushforward f).obj R.F) 1) ≅
      (pushforwardResolution f hf hfinite R).globalCochainComplex.homology 1 := by
  letI : Subsingleton (CategoryTheory.Sheaf.H.{0}
      ((pushforwardResolution f hf hfinite R).K.X 0) 1) :=
    pushforward_cohomology_subsingleton f hf hfinite (R.K.X 0) 1
  exact (pushforwardResolution f hf hfinite R).h1Iso

/-- Finite-pushforward compatibility needs only the original term's
acyclicity; none is assumed separately for the pushed resolution. -/
theorem h1_forward [Subsingleton (CategoryTheory.Sheaf.H.{0} (R.K.X 0) 1)] :
    forwardHom f hf hfinite R.F 1 ≫ (pushedH1Iso f hf hfinite R).hom = R.h1Iso.hom := by
  let : Subsingleton (CategoryTheory.Sheaf.H.{0}
      ((pushforwardResolution f hf hfinite R).K.X 0) 1) :=
    pushforward_cohomology_subsingleton f hf hfinite (R.K.X 0) 1
  exact h1_forward_native f hf hfinite R

end Wikipedia.HopfProblem.ConstantSheafSingularComparison.PushforwardExt
