import Wikipedia.HopfProblem.PeriodTorusExponentialChernWindingCoefficientBasic
import Wikipedia.HopfProblem.PeriodTorusExponentialChernWindingCoefficientRepresentatives

/-!
# The native winding class under the original exponential coefficient map

The canonical additive homology class of the literal complex winding
cochain is the actual coefficient image of the original integral Chern
class.  The comparison follows the original exact forgetful homology
isomorphism and the actual cochain-map naturality on representatives.
No rank calculation or assigned-class definition enters this equality.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.PeriodTorusExponentialChern

open ConstantSheafSingularComparison SheafHigherDirectImage
open PeriodTorusAppellHumbert

variable {p : PeriodDomain} (F : FactorOfAutomorphy p)

/-- The original coefficient-induced homology map sends the original
native winding class to the canonical class of its literal cochain image. -/
theorem exponentialH2Hom_firstChernClass :
    Coefficients.exponentialH2Hom p (PeriodTorusLineBundle.Chern.firstChernClass F) =
      ExtBridge.cycleClass (singularCochainComplex p.Torus (AddCommGrpCat.of ℂ)) 2
        (windingComplexCochain F) (windingComplexCochain_closed_sc F) := by
  change Coefficients.exponentialH2Map p
    (PeriodTorusLineBundle.Chern.firstChernClass F) = _
  rw [Coefficients.exponentialH2Map_eq_native_cochain_map]
  change HomologicalComplex.homologyMap (Coefficients.exponentialCochainMap p) 2
      ((forgetIntegralHomologyIso
        (SingularCohomologyFree.singularCochainComplex p.Torus) 2).inv
          (SingularCohomologyFree.cocycleClass
            (SingularCohomologyFree.singularCochainComplex p.Torus) 2
              (PeriodTorusLineBundle.Chern.firstChernCocycle F))) = _
  rw [forgetIntegralHomologyIso_inv_cocycleClass]
  exact ExtBridge.homologyMap_cycleClass (Coefficients.exponentialCochainMap p) 2
    (PeriodTorusLineBundle.Chern.firstChernCocycle F).val
    (PeriodTorusLineBundle.Chern.firstChernCocycle F).property
    (windingComplexCochain_closed_sc F)

end Wikipedia.HopfProblem.PeriodTorusExponentialChern
