import Wikipedia.HopfProblem.ConstantSheafSingularComparisonSingularScalars

/-!
# Actual singular pullbacks are complex-linear

The scalar actions are the existing actions induced by multiplication
of the original complex coefficient group. The pullback is the native
homology map of the original continuous-map singular cochain pullback.
Coefficient naturality proves its linearity in every degree, on
arbitrary spaces, without using a sheaf-cohomology comparison.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-- The original singular-cohomology pullback intertwines the actual
scalar endomorphisms induced by coefficient multiplication. -/
@[reassoc]
theorem singularPullback_scalar_naturality (f : C(X, Y)) (n : ℕ) (c : ℂ) :
    (singularCohomologyScalarEnd Y n c).asHom ≫
        HomologicalComplex.homologyMap (singularPullback (AddCommGrpCat.of ℂ) f) n =
      HomologicalComplex.homologyMap (singularPullback (AddCommGrpCat.of ℂ) f) n ≫
        (singularCohomologyScalarEnd X n c).asHom := by
  change HomologicalComplex.homologyMap
      (coefficientMap Y (OriginalConstants.complexScalarCoefficient c)) n ≫
        HomologicalComplex.homologyMap (singularPullback (AddCommGrpCat.of ℂ) f) n =
    HomologicalComplex.homologyMap (singularPullback (AddCommGrpCat.of ℂ) f) n ≫
      HomologicalComplex.homologyMap
        (coefficientMap X (OriginalConstants.complexScalarCoefficient c)) n
  have h := congrArg
    (fun g : singularCochainComplex Y (AddCommGrpCat.of ℂ) ⟶
        singularCochainComplex X (AddCommGrpCat.of ℂ) => HomologicalComplex.homologyMap g n)
    (coefficientMap_naturality (OriginalConstants.complexScalarCoefficient c) f).symm
  simpa only [HomologicalComplex.homologyMap_comp] using h

/-- Scalar multiplication commutes with the literal original homology
map for the already fixed singular cohomology modules. -/
theorem singularPullback_homology_smul (f : C(X, Y)) (n : ℕ) (c : ℂ)
    (ξ : (singularCochainComplex Y (AddCommGrpCat.of ℂ)).homology n) :
    letI := singularCohomologyModule Y n
    letI := singularCohomologyModule X n
    HomologicalComplex.homologyMap (singularPullback (AddCommGrpCat.of ℂ) f) n (c • ξ) =
      c • HomologicalComplex.homologyMap (singularPullback (AddCommGrpCat.of ℂ) f) n ξ :=
  ConcreteCategory.congr_hom (singularPullback_scalar_naturality f n c) ξ

/-- The actual continuous-map pullback, bundled as a complex-linear
map for its original source and target scalar actions. -/
def singularPullbackLinearMap (f : C(X, Y)) (n : ℕ) :
    letI := singularCohomologyModule Y n
    letI := singularCohomologyModule X n
    (singularCochainComplex Y (AddCommGrpCat.of ℂ)).homology n →ₗ[ℂ]
      (singularCochainComplex X (AddCommGrpCat.of ℂ)).homology n := by
  letI := singularCohomologyModule Y n
  letI := singularCohomologyModule X n
  exact
    { toFun := HomologicalComplex.homologyMap (singularPullback (AddCommGrpCat.of ℂ) f) n
      map_add' :=
        (HomologicalComplex.homologyMap (singularPullback (AddCommGrpCat.of ℂ) f) n).hom.map_add
      map_smul' := singularPullback_homology_smul f n }

/-- Forgetting linearity returns exactly the original additive homology map. -/
@[simp]
theorem singularPullbackLinearMap_toAddMonoidHom (f : C(X, Y)) (n : ℕ) :
    letI := singularCohomologyModule Y n
    letI := singularCohomologyModule X n
    (singularPullbackLinearMap f n).toAddMonoidHom =
      (HomologicalComplex.homologyMap (singularPullback (AddCommGrpCat.of ℂ) f) n).hom := rfl

/-- The bundled linear map has the original homology map as its literal value. -/
@[simp]
theorem singularPullbackLinearMap_apply (f : C(X, Y)) (n : ℕ)
    (ξ : (singularCochainComplex Y (AddCommGrpCat.of ℂ)).homology n) :
    letI := singularCohomologyModule Y n
    letI := singularCohomologyModule X n
    singularPullbackLinearMap f n ξ =
      HomologicalComplex.homologyMap (singularPullback (AddCommGrpCat.of ℂ) f) n ξ := rfl

end Wikipedia.HopfProblem.ConstantSheafSingularComparison
