import Wikipedia.HopfProblem.ConstantSheafSingularComparisonSingularScalarsCoefficientFunctor
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonOriginalConstantsScalarBasic
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyScalars

/-!
# Actual complex scalar multiplication on native singular cohomology

Literal multiplication of the complex coefficient group gives scalar
endomorphisms after applying the actual additive coefficient functor
and native homology.  Evaluating those endomorphisms defines the complex
module structure on the existing cohomology group.  This construction
uses no sheaf-cohomology comparison or dimension calculation.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison

open CuspNormalization.SheafCohomology

variable (X : Type) [TopologicalSpace X] (n : ℕ)

/-- The endomorphism action obtained by applying the genuine additive
coefficient/cohomology functor to the original complex scalar maps. -/
def singularCohomologyScalarEnd :
    ℂ →+* End ((singularCochainComplex X (AddCommGrpCat.of ℂ)).homology n) :=
  (mapEndRingHom (coefficientCohomologyFunctor X n) (AddCommGrpCat.of ℂ)).comp
    OriginalConstants.complexScalarCoefficientEnd

/-- Every scalar endomorphism is the native cohomology map of the
original coefficient multiplication. -/
@[simp]
theorem singularCohomologyScalarEnd_asHom (c : ℂ) :
    (singularCohomologyScalarEnd X n c).asHom =
      HomologicalComplex.homologyMap
        (coefficientMap X (OriginalConstants.complexScalarCoefficient c)) n := rfl

/-- The actual scalar-induced complex module structure on native
singular cohomology.  This is explicit, not a global instance. -/
@[instance_reducible]
def singularCohomologyModule :
    Module ℂ ((singularCochainComplex X (AddCommGrpCat.of ℂ)).homology n) :=
  moduleOfScalarEnd ((singularCochainComplex X (AddCommGrpCat.of ℂ)).homology n)
    (singularCohomologyScalarEnd X n)

/-- Scalar multiplication is precisely the map induced by literal
multiplication of the original complex coefficient group. -/
theorem singularCohomologyModule_smul (c : ℂ)
    (ξ : (singularCochainComplex X (AddCommGrpCat.of ℂ)).homology n) :
    letI := singularCohomologyModule X n
    c • ξ = HomologicalComplex.homologyMap
      (coefficientMap X (OriginalConstants.complexScalarCoefficient c)) n ξ := rfl

end Wikipedia.HopfProblem.ConstantSheafSingularComparison
