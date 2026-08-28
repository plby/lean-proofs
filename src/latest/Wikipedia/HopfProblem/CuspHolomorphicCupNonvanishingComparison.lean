import Wikipedia.HopfProblem.CuspHolomorphicCupNonvanishingClasses
import Wikipedia.HopfProblem.SheafSingularCupComparison

/-!
# The original cusp comparison carries the named constant cup to the base class

The actual compactness, Hausdorff property, and local contractibility of
the original central fibre instantiate the proved multiplicative
comparison. Its value on the original two integral one-classes is the
complex coefficient image of the actual base-torus dual.
-/

noncomputable section

open CategoryTheory
open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspHolomorphicCupNonvanishing

open CuspNormalization SheafResolution SheafCohomologyConstantEdge
open ConstantSheafSingularComparison CuspQuotient ToricSpace SheafCupProduct

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))
  (hR : SmallDrift C r)

/-- Multiplicativity for the original constant sheaf on the actual cusp central fibre. -/
theorem cuspComplexSheafH2Iso_cup
    (a b : CategoryTheory.Sheaf.H.{0} (constantSheaf C r) 1) :
    (cuspComplexSheafH2Iso C r hr hr1 hC hR).hom
        (constantCup (TopCat.of (CentralSpace C r)) a b) =
      SheafSingularCupComparison.Singular.cupProduct (CentralSpace C r)
        ((cuspComplexSheafH1Iso C r hr hr1 hC hR).hom a)
        ((cuspComplexSheafH1Iso C r hr hr1 hC hR).hom b) := by
  let := cuspCentralSpace_compactSpace C r hr hr1 hC hR
  let := cuspCentralSpace_t2Space C r hr hr1 hC hR
  exact SheafSingularCupComparison.complexSheafH2Iso_cup
    (TopCat.of (CentralSpace C r))
    (CuspLocallyContractible.centralSpace_locallyContractible C r hr hr1 hC hR) a b

/-- The named constant cup maps to the original geometric base-torus class. -/
theorem comparison_constantGamma_cup_constantU :
    (cuspComplexSheafH2Iso C r hr hr1 hC hR).hom
        (constantCup (TopCat.of (CentralSpace C r))
          (constantGamma C r hr hr1 hC hR) (constantU C r hr hr1 hC hR)) =
      complexBase C r hr hC := by
  calc
    _ = SheafSingularCupComparison.Singular.cupProduct (CentralSpace C r)
        ((cuspComplexSheafH1Iso C r hr hr1 hC hR).hom (constantGamma C r hr hr1 hC hR))
        ((cuspComplexSheafH1Iso C r hr hr1 hC hR).hom (constantU C r hr hr1 hC hR)) :=
      cuspComplexSheafH2Iso_cup C r hr hr1 hC hR _ _
    _ = SheafSingularCupComparison.Singular.cupProduct (CentralSpace C r)
        (complexGamma C r hr hC) (complexU C r hr hC) := by
      rw [comparison_constantGamma, comparison_constantU]
    _ = complexBase C r hr hC := (complexBase_eq_cup C r hr hC).symm

/-- The named native constant-sheaf cup is nonzero, detected by the original base torus. -/
theorem constantGamma_cup_constantU_ne_zero :
    constantCup (TopCat.of (CentralSpace C r))
      (constantGamma C r hr hr1 hC hR) (constantU C r hr hr1 hC hR) ≠ 0 := by
  intro h
  apply complexBase_ne_zero C r hr hC
  calc
    complexBase C r hr hC = (cuspComplexSheafH2Iso C r hr hr1 hC hR).hom
        (constantCup (TopCat.of (CentralSpace C r))
          (constantGamma C r hr hr1 hC hR) (constantU C r hr hr1 hC hR)) :=
      (comparison_constantGamma_cup_constantU C r hr hr1 hC hR).symm
    _ = 0 := by rw [h, map_zero]

end Wikipedia.HopfProblem.CuspHolomorphicCupNonvanishing
