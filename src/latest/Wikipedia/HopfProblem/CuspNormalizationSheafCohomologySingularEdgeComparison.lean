import Wikipedia.HopfProblem.ConstantSheafSingularComparison

/-!
# Original complex-linear comparison on the actual cusp

These are the already proved canonical comparisons, specialized using
the actual cusp's proved topological properties. The scalar actions and
the underlying additive isomorphisms are exactly the existing ones.
-/

noncomputable section

open CategoryTheory
open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspNormalization.SheafCohomologySingularEdge

open CuspQuotient ToricSpace SheafResolution ConstantSheafSingularComparison

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
  (hε1 : ε < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
  (hR : SmallDrift C ε)

/-- The actual cusp's original constant-sheaf H¹ comparison, with the
independently defined complex scalar actions. -/
def cuspConstantH1LinearEquiv :
    letI : Module ℂ (CategoryTheory.Sheaf.H.{0} (constantSheaf C ε) 1) :=
      SheafCupProduct.constantCohomologyModule (TopCat.of (CentralSpace C ε)) 1
    letI := singularCohomologyModule (CentralSpace C ε) 1
    CategoryTheory.Sheaf.H.{0} (constantSheaf C ε) 1 ≃ₗ[ℂ]
      (singularCochainComplex (CentralSpace C ε) (AddCommGrpCat.of ℂ)).homology 1 := by
  letI := cuspCentralSpace_compactSpace C ε hε hε1 hC hR
  letI := cuspCentralSpace_t2Space C ε hε hε1 hC hR
  exact complexSheafH1LinearEquiv (TopCat.of (CentralSpace C ε))
    (CuspLocallyContractible.centralSpace_locallyContractible C ε hε hε1 hC hR)

/-- The degree-two comparison uses the same original coefficient action. -/
def cuspConstantH2LinearEquiv :
    letI : Module ℂ (CategoryTheory.Sheaf.H.{0} (constantSheaf C ε) 2) :=
      SheafCupProduct.constantCohomologyModule (TopCat.of (CentralSpace C ε)) 2
    letI := singularCohomologyModule (CentralSpace C ε) 2
    CategoryTheory.Sheaf.H.{0} (constantSheaf C ε) 2 ≃ₗ[ℂ]
      (singularCochainComplex (CentralSpace C ε) (AddCommGrpCat.of ℂ)).homology 2 := by
  letI := cuspCentralSpace_compactSpace C ε hε hε1 hC hR
  letI := cuspCentralSpace_t2Space C ε hε hε1 hC hR
  exact complexSheafH2LinearEquiv (TopCat.of (CentralSpace C ε))
    (CuspLocallyContractible.centralSpace_locallyContractible C ε hε hε1 hC hR)

/-- The degree-one additive isomorphism has not been changed. -/
@[simp] theorem cuspConstantH1LinearEquiv_toAddEquiv :
    letI : Module ℂ (CategoryTheory.Sheaf.H.{0} (constantSheaf C ε) 1) :=
      SheafCupProduct.constantCohomologyModule (TopCat.of (CentralSpace C ε)) 1
    letI := singularCohomologyModule (CentralSpace C ε) 1
    (cuspConstantH1LinearEquiv C ε hε hε1 hC hR).toAddEquiv =
      (cuspComplexSheafH1Iso C ε hε hε1 hC hR).addCommGroupIsoToAddEquiv := rfl

/-- The degree-two additive isomorphism is literally the old comparison. -/
@[simp] theorem cuspConstantH2LinearEquiv_toAddEquiv :
    letI : Module ℂ (CategoryTheory.Sheaf.H.{0} (constantSheaf C ε) 2) :=
      SheafCupProduct.constantCohomologyModule (TopCat.of (CentralSpace C ε)) 2
    letI := singularCohomologyModule (CentralSpace C ε) 2
    (cuspConstantH2LinearEquiv C ε hε hε1 hC hR).toAddEquiv =
      (cuspComplexSheafH2Iso C ε hε hε1 hC hR).addCommGroupIsoToAddEquiv := rfl

end Wikipedia.HopfProblem.CuspNormalization.SheafCohomologySingularEdge
