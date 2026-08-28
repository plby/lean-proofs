import Wikipedia.HopfProblem.ConstantSheafSingularComparisonPushforwardExtFunctorConnecting
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyResolutionExtNaturality

/-!
# Degree-two naturality for exact-functor Ext comparison

The comparison induced by the actual exact functor and the source morphism
commutes with the canonical cokernel description of degree-two Ext. The proof
uses the genuine connecting representatives of both augmented resolutions.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyResolution

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison.PushforwardExtFunctor

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasExt.{0} C] [HasExt.{0} D]
  (G : C ⥤ D) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  {V : C} {A : D} (η : A ⟶ G.obj V) (R : AugmentedResolution C)

/-- The literal cokernel map induced by degree-zero Ext comparison
on the final two terms of the augmented resolution. -/
def extCokernelMap :
    cokernel (R.extZeroComplex V).g ⟶
      cokernel ((mappedResolution G R).extZeroComplex A).g :=
  cokernel.map (R.extZeroComplex V).g ((mappedResolution G R).extZeroComplex A).g
    (extZeroMap G η R).τ₂ (extZeroMap G η R).τ₃ (extZeroMap G η R).comm₂₃.symm

@[reassoc (attr := simp)] theorem extCokernelMap_π :
    cokernel.π (R.extZeroComplex V).g ≫ extCokernelMap G η R =
      comparisonHom G η R.complex.X₃ 0 ≫
        cokernel.π ((mappedResolution G R).extZeroComplex A).g :=
  cokernel.π_desc _ _ _

/-- The native degree-two Ext comparison agrees with the actual cokernel
map. All acyclicity hypotheses concern genuine Ext groups of the terms. -/
@[reassoc] theorem extTwoIso_naturality
    [Subsingleton (Ext V R.complex.X₁ 1)] [Subsingleton (Ext V R.complex.X₁ 2)]
    [Subsingleton (Ext V R.complex.X₂ 1)]
    [Subsingleton (Ext A (mappedResolution G R).complex.X₁ 1)]
    [Subsingleton (Ext A (mappedResolution G R).complex.X₁ 2)]
    [Subsingleton (Ext A (mappedResolution G R).complex.X₂ 1)] :
    comparisonHom G η R.F 2 ≫ ((mappedResolution G R).extTwoIso A).hom =
      (R.extTwoIso V).hom ≫ extCokernelMap G η R := by
  have : Epi (AddCommGrpCat.ofHom (R.connectingTwo V)) :=
    (AddCommGrpCat.epi_iff_surjective _).mpr (R.connectingTwo_surjective V)
  exact comparison_naturality_of_epi
    (AddCommGrpCat.ofHom (R.connectingTwo V))
    (AddCommGrpCat.ofHom ((mappedResolution G R).connectingTwo A))
    (R.extTwoIso V).hom ((mappedResolution G R).extTwoIso A).hom
    (cokernel.π (R.extZeroComplex V).g)
    (cokernel.π ((mappedResolution G R).extZeroComplex A).g)
    (comparisonHom G η R.complex.X₃ 0) (comparisonHom G η R.F 2)
    (extCokernelMap G η R) (connectingTwo_naturality G η R)
    (R.extTwoIso_connecting V) ((mappedResolution G R).extTwoIso_connecting A)
    (extCokernelMap_π G η R).symm

end Wikipedia.HopfProblem.ConstantSheafSingularComparison.PushforwardExtFunctor
