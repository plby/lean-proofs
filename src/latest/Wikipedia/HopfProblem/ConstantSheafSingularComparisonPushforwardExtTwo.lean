import Wikipedia.HopfProblem.ConstantSheafSingularComparisonPushforwardExtOne
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonPushforwardExtAugmented
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonPushforwardExtCycles
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonPushforwardExtTwoComposite

/-!
# Native degree-two cochain-resolution comparison under finite pushforward
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

/-- The original canonical `LowExt` degree-two comparison commutes
with the native finite-pushforward cohomology map. -/
theorem h2_forward_native
    [Subsingleton (CategoryTheory.Sheaf.H.{0} (R.K.X 0) 1)]
    [Subsingleton (CategoryTheory.Sheaf.H.{0} (R.K.X 0) 2)]
    [Subsingleton (CategoryTheory.Sheaf.H.{0} (R.K.X 1) 1)]
    [Subsingleton (CategoryTheory.Sheaf.H.{0}
      ((pushforwardResolution f hf hfinite R).K.X 0) 1)]
    [Subsingleton (CategoryTheory.Sheaf.H.{0}
      ((pushforwardResolution f hf hfinite R).K.X 0) 2)]
    [Subsingleton (CategoryTheory.Sheaf.H.{0}
      ((pushforwardResolution f hf hfinite R).K.X 1) 1)] :
    forwardHom f hf hfinite R.F 2 ≫
        (pushforwardResolution f hf hfinite R).h2Iso.hom = R.h2Iso.hom := by
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} R.truncation.complex.X₁ 1) :=
    ‹Subsingleton (CategoryTheory.Sheaf.H.{0} (R.K.X 0) 1)›
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} R.truncation.complex.X₁ 2) :=
    ‹Subsingleton (CategoryTheory.Sheaf.H.{0} (R.K.X 0) 2)›
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} R.truncation.complex.X₂ 1) :=
    ‹Subsingleton (CategoryTheory.Sheaf.H.{0} (R.K.X 1) 1)›
  let : Subsingleton (CategoryTheory.Sheaf.H.{0}
      (pushforwardResolution f hf hfinite R).truncation.complex.X₁ 1) :=
    ‹Subsingleton (CategoryTheory.Sheaf.H.{0}
      ((pushforwardResolution f hf hfinite R).K.X 0) 1)›
  let : Subsingleton (CategoryTheory.Sheaf.H.{0}
      (pushforwardResolution f hf hfinite R).truncation.complex.X₁ 2) :=
    ‹Subsingleton (CategoryTheory.Sheaf.H.{0}
      ((pushforwardResolution f hf hfinite R).K.X 0) 2)›
  let : Subsingleton (CategoryTheory.Sheaf.H.{0}
      (pushforwardResolution f hf hfinite R).truncation.complex.X₂ 1) :=
    ‹Subsingleton (CategoryTheory.Sheaf.H.{0}
      ((pushforwardResolution f hf hfinite R).K.X 1) 1)›
  have h := h2_forward_composite f hf hfinite R
  exact (congrArg (fun k => forwardHom f hf hfinite R.F 2 ≫ k)
    (cochain_h2Iso_hom (pushforwardResolution f hf hfinite R))).trans
      (h.trans (cochain_h2Iso_hom R).symm)

/-- The same canonical degree-two isomorphism for the pushed
resolution, with its three vanishing conditions proved by native
finite-pushforward cohomology rather than separately assumed. -/
def pushedH2Iso [Subsingleton (CategoryTheory.Sheaf.H.{0} (R.K.X 0) 1)]
    [Subsingleton (CategoryTheory.Sheaf.H.{0} (R.K.X 0) 2)]
    [Subsingleton (CategoryTheory.Sheaf.H.{0} (R.K.X 1) 1)] :
    AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0} ((pushforward f).obj R.F) 2) ≅
      (pushforwardResolution f hf hfinite R).globalCochainComplex.homology 2 := by
  letI : Subsingleton (CategoryTheory.Sheaf.H.{0}
      ((pushforwardResolution f hf hfinite R).K.X 0) 1) :=
    pushforward_cohomology_subsingleton f hf hfinite (R.K.X 0) 1
  letI : Subsingleton (CategoryTheory.Sheaf.H.{0}
      ((pushforwardResolution f hf hfinite R).K.X 0) 2) :=
    pushforward_cohomology_subsingleton f hf hfinite (R.K.X 0) 2
  letI : Subsingleton (CategoryTheory.Sheaf.H.{0}
      ((pushforwardResolution f hf hfinite R).K.X 1) 1) :=
    pushforward_cohomology_subsingleton f hf hfinite (R.K.X 1) 1
  exact (pushforwardResolution f hf hfinite R).h2Iso

/-- Finite-pushforward compatibility requires only the original
resolution's three low-degree acyclicity conditions. -/
theorem h2_forward
    [Subsingleton (CategoryTheory.Sheaf.H.{0} (R.K.X 0) 1)]
    [Subsingleton (CategoryTheory.Sheaf.H.{0} (R.K.X 0) 2)]
    [Subsingleton (CategoryTheory.Sheaf.H.{0} (R.K.X 1) 1)] :
    forwardHom f hf hfinite R.F 2 ≫ (pushedH2Iso f hf hfinite R).hom = R.h2Iso.hom := by
  let : Subsingleton (CategoryTheory.Sheaf.H.{0}
      ((pushforwardResolution f hf hfinite R).K.X 0) 1) :=
    pushforward_cohomology_subsingleton f hf hfinite (R.K.X 0) 1
  let : Subsingleton (CategoryTheory.Sheaf.H.{0}
      ((pushforwardResolution f hf hfinite R).K.X 0) 2) :=
    pushforward_cohomology_subsingleton f hf hfinite (R.K.X 0) 2
  let : Subsingleton (CategoryTheory.Sheaf.H.{0}
      ((pushforwardResolution f hf hfinite R).K.X 1) 1) :=
    pushforward_cohomology_subsingleton f hf hfinite (R.K.X 1) 1
  exact h2_forward_native f hf hfinite R

end Wikipedia.HopfProblem.ConstantSheafSingularComparison.PushforwardExt
