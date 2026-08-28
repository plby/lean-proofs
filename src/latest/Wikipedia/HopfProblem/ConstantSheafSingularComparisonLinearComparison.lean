import Wikipedia.HopfProblem.ConstantSheafSingularComparisonLinearComparisonScalars
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonSingularScalars
import Wikipedia.HopfProblem.SheafCupProductFunctionsLinear

/-!
# The original complex sheaf--singular comparisons are linear

The source uses the existing module action induced by multiplication of
the original constant sheaf's actual sections. The target uses the
module action induced by literal coefficient multiplication on original
singular cochains. The previously constructed additive comparisons are
linear for these independently defined actions. Their underlying
additive equivalences are unchanged.
-/

noncomputable section

open CategoryTheory TopologicalSpace

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison

open CuspNormalization.SheafConstants CuspNormalization.SheafCohomology

variable (X : TopCat.{0}) [CompactSpace X] [T2Space X]

/-- The original H¹ additive comparison is complex-linear for the
actual source and target scalar actions. -/
def complexSheafH1LinearEquiv (hLC : LocallyContractibleSpace X) :
    letI := SheafCupProduct.constantCohomologyModule X 1
    letI := singularCohomologyModule X 1
    CategoryTheory.Sheaf.H.{0} (complexAdditiveSheaf X) 1 ≃ₗ[ℂ]
      (singularCochainComplex X (AddCommGrpCat.of ℂ)).homology 1 := by
  letI := SheafCupProduct.constantCohomologyModule X 1
  letI := singularCohomologyModule X 1
  exact LinearComparison.linearEquivOfScalarEnd
    (AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0} (complexAdditiveSheaf X) 1))
    ((singularCochainComplex X (AddCommGrpCat.of ℂ)).homology 1)
    ((mapEndRingHom (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) 1)
      (complexAdditiveSheaf X)).comp (SheafCupProduct.constantScalarEnd X))
    (singularCohomologyScalarEnd X 1) (complexSheafH1Iso X hLC)
    (fun c => complexSheafH1Iso_scalar_naturality X hLC c)

/-- The original H² additive comparison is complex-linear for the
same actual scalar actions, without any cup-product compatibility assumption. -/
def complexSheafH2LinearEquiv (hLC : LocallyContractibleSpace X) :
    letI := SheafCupProduct.constantCohomologyModule X 2
    letI := singularCohomologyModule X 2
    CategoryTheory.Sheaf.H.{0} (complexAdditiveSheaf X) 2 ≃ₗ[ℂ]
      (singularCochainComplex X (AddCommGrpCat.of ℂ)).homology 2 := by
  letI := SheafCupProduct.constantCohomologyModule X 2
  letI := singularCohomologyModule X 2
  exact LinearComparison.linearEquivOfScalarEnd
    (AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0} (complexAdditiveSheaf X) 2))
    ((singularCochainComplex X (AddCommGrpCat.of ℂ)).homology 2)
    ((mapEndRingHom (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) 2)
      (complexAdditiveSheaf X)).comp (SheafCupProduct.constantScalarEnd X))
    (singularCohomologyScalarEnd X 2) (complexSheafH2Iso X hLC)
    (fun c => complexSheafH2Iso_scalar_naturality X hLC c)

/-- The degree-one linear upgrade has exactly the original additive equivalence. -/
@[simp]
theorem complexSheafH1LinearEquiv_toAddEquiv (hLC : LocallyContractibleSpace X) :
    letI := SheafCupProduct.constantCohomologyModule X 1
    letI := singularCohomologyModule X 1
    (complexSheafH1LinearEquiv X hLC).toAddEquiv = complexSheafH1Equiv X hLC := rfl

/-- The degree-two linear upgrade has exactly the original additive equivalence. -/
@[simp]
theorem complexSheafH2LinearEquiv_toAddEquiv (hLC : LocallyContractibleSpace X) :
    letI := SheafCupProduct.constantCohomologyModule X 2
    letI := singularCohomologyModule X 2
    (complexSheafH2LinearEquiv X hLC).toAddEquiv = complexSheafH2Equiv X hLC := rfl

end Wikipedia.HopfProblem.ConstantSheafSingularComparison
