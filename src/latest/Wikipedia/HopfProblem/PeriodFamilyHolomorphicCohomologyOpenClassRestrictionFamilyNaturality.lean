import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenClassRestrictionFamilyOpen

/-!
# Actual open restriction for globally defined period coefficients

The proved comparison with the original global period class makes
its literal coefficient restrictions natural under every nested base
open. Constant coefficient classes in particular are genuine sections
of the original cohomology presheaf. This statement does not extend
arbitrary functions off a base open or assert a local frame.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.OpenClassRestriction

open PeriodFamilyHigherDirectImage

variable {V : Type*} {B : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace B] [ChartedSpace V B]

/-- Actual globally constant holomorphic coefficient functions. -/
def globalConstantCoefficients (a : Fin 4 → ℂ) : Cocycle.Coefficients V B :=
  fun j => ⟨fun _ => a j, contMDiff_const⟩

/-- Restriction gives the same literal original constant functions on the open. -/
theorem restrict_globalConstantCoefficients (A : Opens B) (a : Fin 4 → ℂ) :
    restrictCoefficients A (globalConstantCoefficients (V := V) (B := B) a) =
      OpenClasses.constantCoefficients A a := rfl

variable [IsManifold (modelWithCornersSelf ℂ V) ω B] [T2Space B]

/-- For original globally defined coefficients, shrinking the base
open is exactly the native cohomology-presheaf restriction. -/
theorem openPeriodClass_restrict_globalCoefficients (P : HolomorphicPeriodMap V B)
    {A W : Opens B} (h : A ≤ W) (a : Cocycle.Coefficients V B) :
    (CategoryTheory.Sheaf.cohomologyPresheaf (Zero.totalAdditiveSheaf P) 1).map
        (homOfLE (Zero.basePreimage_mono P h)).op
        (OpenClasses.periodClass P W (restrictCoefficients W a)) =
      OpenClasses.periodClass P A (restrictCoefficients A a) := by
  exact (congrArg
    ((CategoryTheory.Sheaf.cohomologyPresheaf (Zero.totalAdditiveSheaf P) 1).map
      (homOfLE (Zero.basePreimage_mono P h)).op)
    (openPeriodClass_restrictCoefficients P W a)).trans
    ((GlobalRestriction.restrictionMap_restrict (Zero.totalAdditiveSheaf P)
      (homOfLE (Zero.basePreimage_mono P h)) 1 (Cocycle.periodClass P a)).trans
      (openPeriodClass_restrictCoefficients P A a).symm)

/-- The original neighborhood constant-character class is precisely
restriction of the original global constant-character extension class. -/
theorem constantClass_eq_globalRestriction (P : HolomorphicPeriodMap V B) (A : Opens B)
    (a : Fin 4 → ℂ) :
    OpenClasses.constantClass P A a =
      GlobalRestriction.restrictionMap (Zero.totalAdditiveSheaf P) (Zero.basePreimage P A) 1
        (Cocycle.periodClass P (globalConstantCoefficients (V := V) (B := B) a)) :=
  openPeriodClass_restrictCoefficients P A (globalConstantCoefficients a)

/-- The constructed original constant classes commute with actual
restriction on every pair of nested base opens. -/
theorem constantClass_restrict (P : HolomorphicPeriodMap V B)
    {A W : Opens B} (h : A ≤ W) (a : Fin 4 → ℂ) :
    (CategoryTheory.Sheaf.cohomologyPresheaf (Zero.totalAdditiveSheaf P) 1).map
        (homOfLE (Zero.basePreimage_mono P h)).op (OpenClasses.constantClass P W a) =
      OpenClasses.constantClass P A a :=
  openPeriodClass_restrict_globalCoefficients P h (globalConstantCoefficients a)

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.OpenClassRestriction
