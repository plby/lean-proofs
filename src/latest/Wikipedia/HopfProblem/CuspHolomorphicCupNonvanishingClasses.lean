import Wikipedia.HopfProblem.CuspHolomorphicCupNonvanishingSingular
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonConcreteSpacesCusp
import Wikipedia.HopfProblem.SheafCupProductCuspCompatibility

/-!
# The actual constant and holomorphic cusp one-classes

The classes use the original inverse constant-sheaf/singular comparison
and the original inclusion of constants in the reduced structure sheaf.
No product or nonvanishing is stipulated by these definitions.
-/

noncomputable section

open CategoryTheory
open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspHolomorphicCupNonvanishing

open CuspNormalization SheafResolution SheafCohomologyConstantEdge
open ConstantSheafSingularComparison CuspQuotient ToricSpace

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))
  (hR : SmallDrift C r)

/-- The original class `γ` in the actual constant-sheaf H¹. -/
def constantGamma : CategoryTheory.Sheaf.H.{0} (constantSheaf C r) 1 :=
  (cuspComplexSheafH1Iso C r hr hr1 hC hR).inv (complexGamma C r hr hC)

/-- The original class `u` in the actual constant-sheaf H¹. -/
def constantU : CategoryTheory.Sheaf.H.{0} (constantSheaf C r) 1 :=
  (cuspComplexSheafH1Iso C r hr hr1 hC hR).inv (complexU C r hr hC)

/-- The image of `γ` under the original constants inclusion. -/
def holomorphicGamma : CategoryTheory.Sheaf.H.{0} (reducedSheaf C r hr hr1 hC hR) 1 :=
  (constantsH1Iso C r hr hr1 hC hR).hom (constantGamma C r hr hr1 hC hR)

/-- The image of `u` under the original constants inclusion. -/
def holomorphicU : CategoryTheory.Sheaf.H.{0} (reducedSheaf C r hr hr1 hC hR) 1 :=
  (constantsH1Iso C r hr hr1 hC hR).hom (constantU C r hr hr1 hC hR)

@[simp] theorem comparison_constantGamma :
    (cuspComplexSheafH1Iso C r hr hr1 hC hR).hom (constantGamma C r hr hr1 hC hR) =
      complexGamma C r hr hC :=
  ConcreteCategory.congr_hom (cuspComplexSheafH1Iso C r hr hr1 hC hR).inv_hom_id _

@[simp] theorem comparison_constantU :
    (cuspComplexSheafH1Iso C r hr hr1 hC hR).hom (constantU C r hr hr1 hC hR) =
      complexU C r hr hC :=
  ConcreteCategory.congr_hom (cuspComplexSheafH1Iso C r hr hr1 hC hR).inv_hom_id _

end Wikipedia.HopfProblem.CuspHolomorphicCupNonvanishing
