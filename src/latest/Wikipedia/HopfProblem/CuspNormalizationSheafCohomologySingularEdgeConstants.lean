import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologySingularEdgeConstantsBasic
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyConstantEdgeCusp

/-!
# Original constants-to-holomorphic cohomology maps on the actual cusp

The native coefficient map is complex-linear for the existing scalar
actions. Its already proved degree-one isomorphism receives a linear
upgrade with exactly the same additive equivalence and forward map.
-/

noncomputable section

open CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspNormalization.SheafCohomologySingularEdge

open CuspQuotient ToricCharts ToricSpace SheafResolution
open SheafCohomologyConstantEdge

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
  (hε1 : ε < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
  (hR : SmallDrift C ε)

/-- The actual constants inclusion on cusp cohomology, complex-linear
for the original sheaf-induced scalar actions in every degree. -/
def constantsCohomologyLinearMap (n : ℕ) :
    letI : Module ℂ (CategoryTheory.Sheaf.H.{0} (constantSheaf C ε) n) :=
      SheafCupProduct.constantCohomologyModule (TopCat.of (CentralSpace C ε)) n
    CategoryTheory.Sheaf.H.{0} (constantSheaf C ε) n →ₗ[ℂ]
      CategoryTheory.Sheaf.H.{0} (reducedSheaf C ε hε hε1 hC hR) n := by
  letI := CuspQuotient.chartedSpace C ε hε hε1 hC hR
  exact reducedConstantsCohomologyLinearMap 𝓘(ℂ, CoordinateSpace 3) (centralSet C ε) n

/-- The forward map remains literal native cohomology of the original
constants inclusion into the actual reduced structure sheaf. -/
@[simp] theorem constantsCohomologyLinearMap_toAddMonoidHom (n : ℕ) :
    letI : Module ℂ (CategoryTheory.Sheaf.H.{0} (constantSheaf C ε) n) :=
      SheafCupProduct.constantCohomologyModule (TopCat.of (CentralSpace C ε)) n
    (constantsCohomologyLinearMap C ε hε hε1 hC hR n).toAddMonoidHom =
      CategoryTheory.Sheaf.H.map (reducedConstantsMap C ε hε hε1 hC hR) n := rfl

/-- The old degree-one constants isomorphism is linear for the actual
source and target modules, without changing its underlying map. -/
def constantsH1LinearEquiv :
    letI : Module ℂ (CategoryTheory.Sheaf.H.{0} (constantSheaf C ε) 1) :=
      SheafCupProduct.constantCohomologyModule (TopCat.of (CentralSpace C ε)) 1
    CategoryTheory.Sheaf.H.{0} (constantSheaf C ε) 1 ≃ₗ[ℂ]
      CategoryTheory.Sheaf.H.{0} (reducedSheaf C ε hε hε1 hC hR) 1 := by
  letI : Module ℂ (CategoryTheory.Sheaf.H.{0} (constantSheaf C ε) 1) :=
    SheafCupProduct.constantCohomologyModule (TopCat.of (CentralSpace C ε)) 1
  exact
    { (constantsH1Iso C ε hε hε1 hC hR).addCommGroupIsoToAddEquiv with
      map_smul' := fun c a => (constantsCohomologyLinearMap C ε hε hε1 hC hR 1).map_smul c a }

/-- The linear upgrade is literally the original additive equivalence. -/
@[simp] theorem constantsH1LinearEquiv_toAddEquiv :
    letI : Module ℂ (CategoryTheory.Sheaf.H.{0} (constantSheaf C ε) 1) :=
      SheafCupProduct.constantCohomologyModule (TopCat.of (CentralSpace C ε)) 1
    (constantsH1LinearEquiv C ε hε hε1 hC hR).toAddEquiv =
      (constantsH1Iso C ε hε hε1 hC hR).addCommGroupIsoToAddEquiv := rfl

end Wikipedia.HopfProblem.CuspNormalization.SheafCohomologySingularEdge
