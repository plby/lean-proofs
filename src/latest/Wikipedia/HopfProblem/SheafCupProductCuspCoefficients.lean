import Wikipedia.HopfProblem.SheafCupProductCuspEdge
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyScalarResolutionTerms

/-!
# Original coefficient maps and scalar actions for the fixed cusp atlas

These wrappers retain the actual reduced ring sheaf, its original
pointwise scalar action, and the original constants map. Forgetting the
ring map is literally the coefficient map used by the normalization
resolution and by its native cohomology comparisons.
-/

noncomputable section

open CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SheafCupProduct.Cusp

open GodementRing CuspNormalization SheafResolution
open CuspQuotient ToricCharts ToricSpace

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
  (hε1 : ε < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
  (hR : SmallDrift C ε)

/-- The actual ring-valued constant-to-reduced map for the fixed cusp atlas. -/
def reducedConstantsRingMap :
    SheafConstants.complexSheaf (TopCat.of (CentralSpace C ε)) ⟶
      reducedRingSheaf C ε hε hε1 hC hR := by
  letI := CuspQuotient.chartedSpace C ε hε hε1 hC hR
  exact SheafConstants.reducedMap 𝓘(ℂ, CoordinateSpace 3) (centralSet C ε)

theorem forget_reducedConstantsRingMap :
    (forgetSheaf (TopCat.of (CentralSpace C ε))).map
        (reducedConstantsRingMap C ε hε hε1 hC hR) =
      reducedConstantsMap C ε hε hε1 hC hR := rfl

theorem cohomologyMap_reducedConstantsRingMap (n : ℕ) :
    cohomologyMap (reducedConstantsRingMap C ε hε hε1 hC hR) n =
      CategoryTheory.Sheaf.H.map (reducedConstantsMap C ε hε hε1 hC hR) n := rfl

/-- The actual reduced cusp ring sheaf with its original pointwise scalar action. -/
def holomorphicCuspCup :
    CategoryTheory.Sheaf.H.{0} (reducedSheaf C ε hε hε1 hC hR) 1 →+
      CategoryTheory.Sheaf.H.{0} (reducedSheaf C ε hε hε1 hC hR) 1 →+
        CategoryTheory.Sheaf.H.{0} (reducedSheaf C ε hε hε1 hC hR) 2 :=
  cup (reducedRingSheaf C ε hε hε1 hC hR)
    (SheafCohomologyScalarResolution.reducedSheafScalarEnd C ε hε hε1 hC hR)

/-- The fixed-atlas wrapper is the existing native reduced-function cup. -/
theorem holomorphicCuspCup_eq_reducedCup :
    letI := CuspQuotient.chartedSpace C ε hε hε1 hC hR
    holomorphicCuspCup C ε hε hε1 hC hR =
      SheafCupProduct.reducedCup 𝓘(ℂ, CoordinateSpace 3) (centralSet C ε) := rfl

end Wikipedia.HopfProblem.SheafCupProduct.Cusp
