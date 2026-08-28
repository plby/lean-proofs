import Wikipedia.HopfProblem.ConstantSheafSingularComparisonCoefficientIntegralComplex
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonCochainIntegralCohomology

/-!
# Integral-to-complex coefficients on the original singular cohomology

The original integral cohomology first passes through the canonical
forgetful homology comparison.  The map then comes from the existing
cochain map that casts each original integer value to `ℂ`.  The native
additive/integral cohomology comparison respects this coefficient map,
as do the original continuous-map pullbacks.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison

/-- The actual coefficient inclusion on the original integral singular
cohomology, with values in the original complex-valued singular cohomology. -/
def integralToComplexCohomologyMap (X : Type) [TopologicalSpace X] (n : ℕ) :
    integralForget.obj (SingularCohomologyFree.SingularCohomology X n) ⟶
      (singularCochainComplex X (AddCommGrpCat.of ℂ)).homology n :=
  (forgetIntegralHomologyIso (SingularCohomologyFree.singularCochainComplex X) n).inv ≫
    HomologicalComplex.homologyMap (integralToComplexCochainMap X) n

/-- The original integral-cohomology comparison intertwines the literal
integer-to-complex coefficient map on additive singular cochains. -/
@[reassoc]
theorem integralCohomologyIso_toComplex (X : Type) [TopologicalSpace X] (n : ℕ) :
    (integralCohomologyIso X n).hom ≫ integralToComplexCohomologyMap X n =
      HomologicalComplex.homologyMap (coefficientMap X integerToComplexCoefficient) n := by
  simp only [integralCohomologyIso_hom, integralToComplexCohomologyMap,
    Category.assoc, Iso.hom_inv_id_assoc]
  rw [← HomologicalComplex.homologyMap_comp]
  simp only [integralToComplexCochainMap, Iso.hom_inv_id_assoc]

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-- Coefficient inclusion commutes with the original continuous-map
pullbacks on both the integral and complex cohomology groups. -/
@[reassoc]
theorem integralToComplexCohomologyMap_naturality (f : C(X, Y)) (n : ℕ) :
    integralForget.map
        (HomologicalComplex.homologyMap (SingularCohomologyFree.singularPullback f) n) ≫
        integralToComplexCohomologyMap X n =
      integralToComplexCohomologyMap Y n ≫
        HomologicalComplex.homologyMap (singularPullback (AddCommGrpCat.of ℂ) f) n := by
  have hF :
      integralForget.map
          (HomologicalComplex.homologyMap (SingularCohomologyFree.singularPullback f) n) ≫
          (forgetIntegralHomologyIso (SingularCohomologyFree.singularCochainComplex X) n).inv =
        (forgetIntegralHomologyIso (SingularCohomologyFree.singularCochainComplex Y) n).inv ≫
          HomologicalComplex.homologyMap
            (forgetIntegralCochains.map (SingularCohomologyFree.singularPullback f)) n :=
    ShortComplex.mapHomologyIso_inv_naturality
      ((HomologicalComplex.shortComplexFunctor (ModuleCat.{0} ℤ) (ComplexShape.up ℕ) n).map
        (SingularCohomologyFree.singularPullback f)) integralForget
  have h := congrArg (fun g => HomologicalComplex.homologyMap g n)
    (integralToComplexCochainMap_naturality f)
  simp only [HomologicalComplex.homologyMap_comp] at h
  simp only [integralToComplexCohomologyMap]
  rw [← Category.assoc, hF, Category.assoc, h, ← Category.assoc]

/-- The same coefficient map with the original integral group as its
literal additive-homomorphism domain. -/
def integralToComplexCohomologyHom (X : Type) [TopologicalSpace X] (n : ℕ) :
    SingularCohomologyFree.SingularCohomology X n →+
      (singularCochainComplex X (AddCommGrpCat.of ℂ)).homology n :=
  (integralToComplexCohomologyMap X n).hom

@[simp]
theorem integralToComplexCohomologyHom_apply (X : Type) [TopologicalSpace X] (n : ℕ)
    (ξ : SingularCohomologyFree.SingularCohomology X n) :
    integralToComplexCohomologyHom X n ξ = integralToComplexCohomologyMap X n ξ := rfl

/-- Pointwise compatibility with the original additive/integral comparison. -/
theorem integralCohomologyEquiv_toComplex (X : Type) [TopologicalSpace X] (n : ℕ)
    (ξ : (singularCochainComplex X (AddCommGrpCat.of ℤ)).homology n) :
    integralToComplexCohomologyHom X n (integralCohomologyEquiv X n ξ) =
      HomologicalComplex.homologyMap (coefficientMap X integerToComplexCoefficient) n ξ :=
  ConcreteCategory.congr_hom (integralCohomologyIso_toComplex X n) ξ

/-- Pointwise naturality uses the established original integral pullback. -/
theorem integralToComplexCohomologyHom_naturality (f : C(X, Y)) (n : ℕ)
    (ξ : SingularCohomologyFree.SingularCohomology Y n) :
    integralToComplexCohomologyHom X n
        (SingularCohomologyFree.singularCohomologyPullback f n ξ) =
      HomologicalComplex.homologyMap (singularPullback (AddCommGrpCat.of ℂ) f) n
        (integralToComplexCohomologyHom Y n ξ) :=
  ConcreteCategory.congr_hom (integralToComplexCohomologyMap_naturality f n) ξ

end Wikipedia.HopfProblem.ConstantSheafSingularComparison
