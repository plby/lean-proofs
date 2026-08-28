import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologySingularEdgeConstants
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologySingularEdgeComparison

/-!
# Source Lemma 9.12(iii): the original singular H¹ comparison

The original inclusion of constants induces a complex-linear
isomorphism from the actual singular H¹ of the cusp to the actual Ext
H¹ of its reduced holomorphic structure sheaf.
-/

noncomputable section

open CategoryTheory
open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspNormalization.SheafCohomologySingularEdge

open CuspQuotient ToricSpace SheafResolution ConstantSheafSingularComparison
open SheafCohomologyConstantEdge

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
  (hε1 : ε < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
  (hR : SmallDrift C ε)

/-- The actual singular H¹ to holomorphic H¹ map is a complex-linear
equivalence. Its definition uses the original constants inclusion. -/
def singularH1HolomorphicLinearEquiv :
    letI := singularCohomologyModule (CentralSpace C ε) 1
    (singularCochainComplex (CentralSpace C ε) (AddCommGrpCat.of ℂ)).homology 1 ≃ₗ[ℂ]
      CategoryTheory.Sheaf.H.{0} (reducedSheaf C ε hε hε1 hC hR) 1 := by
  letI : Module ℂ (CategoryTheory.Sheaf.H.{0} (constantSheaf C ε) 1) :=
    SheafCupProduct.constantCohomologyModule (TopCat.of (CentralSpace C ε)) 1
  letI := singularCohomologyModule (CentralSpace C ε) 1
  exact (cuspConstantH1LinearEquiv C ε hε hε1 hC hR).symm.trans
    (constantsH1LinearEquiv C ε hε hε1 hC hR)

/-- The forward map is exactly the original coefficient map after the
canonical singular-to-constant-sheaf comparison. -/
@[simp] theorem singularH1HolomorphicLinearEquiv_apply
    (a : (singularCochainComplex (CentralSpace C ε) (AddCommGrpCat.of ℂ)).homology 1) :
    letI := singularCohomologyModule (CentralSpace C ε) 1
    singularH1HolomorphicLinearEquiv C ε hε hε1 hC hR a =
      CategoryTheory.Sheaf.H.map (reducedConstantsMap C ε hε hε1 hC hR) 1
        ((cuspComplexSheafH1Iso C ε hε hε1 hC hR).inv a) := rfl

/-- The underlying additive equivalence is the original pair of
canonical isomorphisms, with neither a new map nor a new scalar action. -/
@[simp] theorem singularH1HolomorphicLinearEquiv_toAddEquiv :
    letI := singularCohomologyModule (CentralSpace C ε) 1
    (singularH1HolomorphicLinearEquiv C ε hε hε1 hC hR).toAddEquiv =
      ((cuspComplexSheafH1Iso C ε hε hε1 hC hR).symm ≪≫
        constantsH1Iso C ε hε hε1 hC hR).addCommGroupIsoToAddEquiv := rfl

end Wikipedia.HopfProblem.CuspNormalization.SheafCohomologySingularEdge
