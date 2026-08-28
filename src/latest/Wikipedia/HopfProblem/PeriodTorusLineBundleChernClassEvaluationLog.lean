import Wikipedia.HopfProblem.PeriodTorusLineBundleChernCoverProducts
import Wikipedia.HopfProblem.PeriodTorusLineBundleChernLogBasic
import Wikipedia.HopfProblem.PeriodTorusCohomologyAlternatingCoordinates

/-!
# Native cohomology evaluation of actual factor-log cocycles

The covering edge cocycle and the genuine logarithmic factor defect
determine a native singular cohomology class. Its evaluation on the
original positive period-loop products is the actual logarithmic
alternating form. For the canonical Appell--Humbert factor this gives
the positive coefficient class, by the proved native degree-two
cohomology marking. The geometric first Chern class is compared with
the negative of this class in the subsequent module.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusLineBundle.Chern

open FirstHurewicz SingularCohomologyFree PeriodTorusHigherHomologyPontryagin
open PeriodTorusAppellHumbert PeriodTorusTypeOneOne PeriodTorusLineBundleClassification
open PeriodTorusLineBundleChernLog PeriodTorusCohomology ChernCover ChernCocycle

/-- Evaluate the class of the actual factor-log cocycle on the actual
positive period-loop product, with its geometric column marking. -/
theorem factorTwoClass_evaluate_periodLoops {p : PeriodDomain}
    (F : FactorOfAutomorphy p) (x y : Lattice) :
    singularEvaluation p.Torus 2 (twoClass (edgeCocycle p) (factorCoordinateCocycle F))
      (product11 p.Torus (loopHomologyClass (p.periodLoop x))
        (loopHomologyClass (p.periodLoop y))) =
      factorLogAlternatingForm F (p.latticeEquiv.symm x) (p.latticeEquiv.symm y) := by
  rw [twoClass_evaluate_periodLoops, factorCoordinateCocycle_apply,
    factorCoordinateCocycle_apply, factorCocycle_antisymm]

/-- The same evaluation using elements of the genuine period lattice. -/
theorem factorTwoClass_evaluate_lattice {p : PeriodDomain}
    (F : FactorOfAutomorphy p) (l m : p.lattice) :
    singularEvaluation p.Torus 2 (twoClass (edgeCocycle p) (factorCoordinateCocycle F))
      (product11 p.Torus (loopHomologyClass (p.periodLoop (p.latticeEquiv l)))
        (loopHomologyClass (p.periodLoop (p.latticeEquiv m)))) =
      factorLogAlternatingForm F l m := by
  rw [factorTwoClass_evaluate_periodLoops, AddEquiv.symm_apply_apply,
    AddEquiv.symm_apply_apply]

/-- The canonical factor-log class has the positive original integral periods. -/
theorem canonicalTwoClass_evaluate_periodLoops (p : PeriodDomain) (E : Fin 6 → ℤ)
    (hType : IsTypeOneOne (tangentForm p E)) (x y : Lattice) :
    singularEvaluation p.Torus 2
      (twoClass (edgeCocycle p) (factorCoordinateCocycle (integralFactor p E hType)))
      (product11 p.Torus (loopHomologyClass (p.periodLoop x))
        (loopHomologyClass (p.periodLoop y))) = coordinateForm E x y := by
  rw [factorTwoClass_evaluate_periodLoops, canonicalFactorLogAlternatingForm_apply,
    AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]

/-- Native degree-two cohomology, not a replacement cocycle model, identifies
the canonical logarithmic class with the positive coefficient class. -/
theorem canonicalTwoClass_eq_coefficientClass (p : PeriodDomain) (E : Fin 6 → ℤ)
    (hType : IsTypeOneOne (tangentForm p E)) :
    twoClass (edgeCocycle p) (factorCoordinateCocycle (integralFactor p E hType)) =
      coefficientClass p E := by
  apply cohomology_ext_periodLoops p
  intro x y
  rw [canonicalTwoClass_evaluate_periodLoops, coefficientClass_evaluate_periodLoops]

/-- Each of the six canonical coefficients is evaluation on the named positive pair. -/
theorem canonicalTwoClass_evaluate_basis_pair (p : PeriodDomain) (E : Fin 6 → ℤ)
    (hType : IsTypeOneOne (tangentForm p E)) (k : Fin 6) :
    singularEvaluation p.Torus 2
      (twoClass (edgeCocycle p) (factorCoordinateCocycle (integralFactor p E hType)))
      (product11 p.Torus
        (loopHomologyClass (p.periodLoop (Pi.single (coefficientPair k).1 1)))
        (loopHomologyClass (p.periodLoop (Pi.single (coefficientPair k).2 1)))) = E k := by
  rw [canonicalTwoClass_evaluate_periodLoops]
  exact coordinateForm_basis_pair E k

end Wikipedia.HopfProblem.PeriodTorusLineBundle.Chern
