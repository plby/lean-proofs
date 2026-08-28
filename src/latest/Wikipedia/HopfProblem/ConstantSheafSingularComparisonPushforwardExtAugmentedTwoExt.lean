import Wikipedia.HopfProblem.ConstantSheafSingularComparisonPushforwardExtAugmentedBasic

/-!
# The specialized native degree-two Ext square
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison.PushforwardExt

open CuspNormalization.SheafCohomologyResolution
open CuspNormalization.SheafCohomologyFinitePushforward

variable {X Y : TopCat.{0}} [T2Space X] (f : X ⟶ Y)
  (hf : IsClosedMap f) (hfinite : ∀ y : Y, (f ⁻¹' {y}).Finite)
  (R : AugmentedResolution (AbelianSheaf X))

/-- The exact-functor degree-two comparison specialized to the
actual finite closed pushforward and its actual integer-sheaf unit. -/
theorem augmented_extTwo_forward
    [Subsingleton (Ext.{0} (unitSheaf X) R.complex.X₁ 1)]
    [Subsingleton (Ext.{0} (unitSheaf X) R.complex.X₁ 2)]
    [Subsingleton (Ext.{0} (unitSheaf X) R.complex.X₂ 1)]
    [Subsingleton (Ext.{0} (unitSheaf Y)
      (pushforwardAugmentedResolution f hf hfinite R).complex.X₁ 1)]
    [Subsingleton (Ext.{0} (unitSheaf Y)
      (pushforwardAugmentedResolution f hf hfinite R).complex.X₁ 2)]
    [Subsingleton (Ext.{0} (unitSheaf Y)
      (pushforwardAugmentedResolution f hf hfinite R).complex.X₂ 1)] :
    forwardHom f hf hfinite R.F 2 ≫
        ((pushforwardAugmentedResolution f hf hfinite R).extTwoIso (unitSheaf Y)).hom =
      (R.extTwoIso (unitSheaf X)).hom ≫ extCokernelForwardMap f hf hfinite R := by
  let : PreservesFiniteLimits (pushforward f) :=
    (pushforward_preservesFiniteLimitsAndColimits f hf hfinite).1
  let : PreservesFiniteColimits (pushforward f) :=
    pushforward_preservesFiniteColimits f hf hfinite
  let : Subsingleton (Ext.{0} (unitSheaf Y)
      (PushforwardExtFunctor.mappedResolution (pushforward f) R).complex.X₁ 1) :=
    ‹Subsingleton (Ext.{0} (unitSheaf Y)
      (pushforwardAugmentedResolution f hf hfinite R).complex.X₁ 1)›
  let : Subsingleton (Ext.{0} (unitSheaf Y)
      (PushforwardExtFunctor.mappedResolution (pushforward f) R).complex.X₁ 2) :=
    ‹Subsingleton (Ext.{0} (unitSheaf Y)
      (pushforwardAugmentedResolution f hf hfinite R).complex.X₁ 2)›
  let : Subsingleton (Ext.{0} (unitSheaf Y)
      (PushforwardExtFunctor.mappedResolution (pushforward f) R).complex.X₂ 1) :=
    ‹Subsingleton (Ext.{0} (unitSheaf Y)
      (pushforwardAugmentedResolution f hf hfinite R).complex.X₂ 1)›
  exact PushforwardExtFunctor.extTwoIso_naturality
    (V := unitSheaf X) (A := unitSheaf Y) (pushforward f) (integerUnit f) R

end Wikipedia.HopfProblem.ConstantSheafSingularComparison.PushforwardExt
