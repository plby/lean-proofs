import Wikipedia.HopfProblem.ConstantSheafSingularComparisonConcreteCoefficients
import Wikipedia.HopfProblem.CuspLocallyContractible

/-!
# Sheaf--singular comparison on the original cusp central fibre

The base below is the literal central-fibre subspace used by the
normalization sheaf resolution.  Its compactness, Hausdorff property,
and local contractibility follow from the proved cusp construction.
Only that construction's geometric hypotheses occur in the comparisons.
-/

noncomputable section

open CategoryTheory TopologicalSpace
open scoped ContDiff

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison

open CuspQuotient ToricSpace CuspNormalization.SheafResolution CuspNormalization.SheafConstants

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
  (hR : SmallDrift C ε)

include hε hε1 hC hR

/-- Compactness of the actual sheaf-resolution base follows from the
proved proper cusp projection. -/
theorem cuspCentralSpace_compactSpace : CompactSpace (CentralSpace C ε) :=
  isCompact_iff_compactSpace.mp (central_fibre_compact C ε hε hε1 hC hR)

/-- The actual central-fibre subspace is Hausdorff in its original topology. -/
theorem cuspCentralSpace_t2Space : T2Space (CentralSpace C ε) := by
  let := quotient_t2Space C ε hε hε1 hC hR
  infer_instance

/-- Genuine H¹ of the constant sheaf on the original singular cusp,
with arbitrary abelian coefficients. -/
def cuspConstantSheafH1Iso (A : AddCommGrpCat.{0}) :
    AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0}
      (ConstantSheafFirstCohomology.Constant.sheaf (TopCat.of (CentralSpace C ε)) A) 1) ≅
        (singularCochainComplex (CentralSpace C ε) A).homology 1 := by
  letI := cuspCentralSpace_compactSpace C ε hε hε1 hC hR
  letI := cuspCentralSpace_t2Space C ε hε hε1 hC hR
  exact constantSheafH1Iso (TopCat.of (CentralSpace C ε)) A
    (CuspLocallyContractible.centralSpace_locallyContractible C ε hε hε1 hC hR)

/-- Genuine H² of the constant sheaf on the original singular cusp. -/
def cuspConstantSheafH2Iso (A : AddCommGrpCat.{0}) :
    AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0}
      (ConstantSheafFirstCohomology.Constant.sheaf (TopCat.of (CentralSpace C ε)) A) 2) ≅
        (singularCochainComplex (CentralSpace C ε) A).homology 2 := by
  letI := cuspCentralSpace_compactSpace C ε hε hε1 hC hR
  letI := cuspCentralSpace_t2Space C ε hε hε1 hC hR
  exact constantSheafH2Iso (TopCat.of (CentralSpace C ε)) A
    (CuspLocallyContractible.centralSpace_locallyContractible C ε hε hε1 hC hR)

/-- The cusp H¹ comparison starts with the manuscript's original
constant complex sheaf, not a replacement source. -/
def cuspComplexSheafH1Iso :
    AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0}
      (complexAdditiveSheaf (TopCat.of (CentralSpace C ε))) 1) ≅
        (singularCochainComplex (CentralSpace C ε) (AddCommGrpCat.of ℂ)).homology 1 := by
  letI := cuspCentralSpace_compactSpace C ε hε hε1 hC hR
  letI := cuspCentralSpace_t2Space C ε hε hε1 hC hR
  exact complexSheafH1Iso (TopCat.of (CentralSpace C ε))
    (CuspLocallyContractible.centralSpace_locallyContractible C ε hε hε1 hC hR)

/-- The original constant complex sheaf on the cusp has the actual
complex-valued singular H² as its genuine Ext cohomology. -/
def cuspComplexSheafH2Iso :
    AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0}
      (complexAdditiveSheaf (TopCat.of (CentralSpace C ε))) 2) ≅
        (singularCochainComplex (CentralSpace C ε) (AddCommGrpCat.of ℂ)).homology 2 := by
  letI := cuspCentralSpace_compactSpace C ε hε hε1 hC hR
  letI := cuspCentralSpace_t2Space C ε hε hε1 hC hR
  exact complexSheafH2Iso (TopCat.of (CentralSpace C ε))
    (CuspLocallyContractible.centralSpace_locallyContractible C ε hε hε1 hC hR)

/-- The integral cusp comparison ends with the original integer-linear
singular cohomology group in degree one. -/
def cuspIntegralSheafH1Equiv :
    CategoryTheory.Sheaf.H.{0}
      (ConstantSheafFirstCohomology.Constant.sheaf (TopCat.of (CentralSpace C ε))
        (AddCommGrpCat.of ℤ)) 1 ≃+
      SingularCohomologyFree.SingularCohomology (CentralSpace C ε) 1 := by
  letI := cuspCentralSpace_compactSpace C ε hε hε1 hC hR
  letI := cuspCentralSpace_t2Space C ε hε hε1 hC hR
  exact integralSheafH1Equiv (TopCat.of (CentralSpace C ε))
    (CuspLocallyContractible.centralSpace_locallyContractible C ε hε hε1 hC hR)

/-- The integral cusp comparison ends with the original degree-two
integer-linear singular cohomology group. -/
def cuspIntegralSheafH2Equiv :
    CategoryTheory.Sheaf.H.{0}
      (ConstantSheafFirstCohomology.Constant.sheaf (TopCat.of (CentralSpace C ε))
        (AddCommGrpCat.of ℤ)) 2 ≃+
      SingularCohomologyFree.SingularCohomology (CentralSpace C ε) 2 := by
  letI := cuspCentralSpace_compactSpace C ε hε hε1 hC hR
  letI := cuspCentralSpace_t2Space C ε hε hε1 hC hR
  exact integralSheafH2Equiv (TopCat.of (CentralSpace C ε))
    (CuspLocallyContractible.centralSpace_locallyContractible C ε hε hε1 hC hR)

end Wikipedia.HopfProblem.ConstantSheafSingularComparison
