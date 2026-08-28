import Wikipedia.HopfProblem.PeriodTorusLineBundleChernClass
import Wikipedia.HopfProblem.PeriodTorusLineBundleChernClassEvaluationLog
import Wikipedia.HopfProblem.PeriodTorusAppellHumbertFactorMultiplicativity

/-!
# Integral periods of the genuine first Chern class

The actual native boundary-winding construction of the first Chern
class has the negative logarithmic alternating periods. Its canonical
Appell--Humbert specialization is therefore the negative coefficient
class, with signs fixed by the positive period loops and the original
diagonal factor action. Applying the construction to the negative
coefficient vector realizes the positive class.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusLineBundle.Chern

open FirstHurewicz SingularCohomologyFree PeriodTorusHigherHomologyPontryagin
open PeriodTorusAppellHumbert PeriodTorusTypeOneOne PeriodTorusLineBundleClassification
open PeriodTorusCohomology

/-- The first Chern class of the actual native factor bundle has the
negative alternating periods of its genuine factor logarithms. -/
theorem firstChernClass_evaluate_periodLoops {p : PeriodDomain}
    (F : FactorOfAutomorphy p) (x y : Lattice) :
    singularEvaluation p.Torus 2 (firstChernClass F)
      (product11 p.Torus (loopHomologyClass (p.periodLoop x))
        (loopHomologyClass (p.periodLoop y))) =
      -factorLogAlternatingForm F (p.latticeEquiv.symm x) (p.latticeEquiv.symm y) := by
  rw [firstChernClass_eq_neg_twoClass, map_neg, LinearMap.neg_apply,
    factorTwoClass_evaluate_periodLoops]

/-- The same genuine Chern-class evaluation in the actual period lattice. -/
theorem firstChernClass_evaluate_lattice {p : PeriodDomain}
    (F : FactorOfAutomorphy p) (l m : p.lattice) :
    singularEvaluation p.Torus 2 (firstChernClass F)
      (product11 p.Torus (loopHomologyClass (p.periodLoop (p.latticeEquiv l)))
        (loopHomologyClass (p.periodLoop (p.latticeEquiv m)))) =
      -factorLogAlternatingForm F l m := by
  rw [firstChernClass_evaluate_periodLoops, AddEquiv.symm_apply_apply,
    AddEquiv.symm_apply_apply]

/-- The original positive-translation Appell--Humbert convention gives
minus the original coefficient class, as an equality in actual singular cohomology. -/
theorem firstChernClass_integralFactor (p : PeriodDomain) (E : Fin 6 → ℤ)
    (hType : IsTypeOneOne (tangentForm p E)) :
    firstChernClass (integralFactor p E hType) = -coefficientClass p E := by
  rw [firstChernClass_eq_neg_twoClass, canonicalTwoClass_eq_coefficientClass]

theorem firstChernClass_integralFactor_evaluate_periodLoops
    (p : PeriodDomain) (E : Fin 6 → ℤ) (hType : IsTypeOneOne (tangentForm p E))
    (x y : Lattice) :
    singularEvaluation p.Torus 2 (firstChernClass (integralFactor p E hType))
      (product11 p.Torus (loopHomologyClass (p.periodLoop x))
        (loopHomologyClass (p.periodLoop y))) = -coordinateForm E x y := by
  rw [firstChernClass_integralFactor, map_neg, LinearMap.neg_apply,
    coefficientClass_evaluate_periodLoops]

/-- The six named positive period-pair cycles have Chern numbers `-E k`. -/
theorem firstChernClass_integralFactor_evaluate_basis_pair
    (p : PeriodDomain) (E : Fin 6 → ℤ) (hType : IsTypeOneOne (tangentForm p E))
    (k : Fin 6) :
    singularEvaluation p.Torus 2 (firstChernClass (integralFactor p E hType))
      (product11 p.Torus
        (loopHomologyClass (p.periodLoop (Pi.single (coefficientPair k).1 1)))
        (loopHomologyClass (p.periodLoop (Pi.single (coefficientPair k).2 1)))) = -E k := by
  rw [firstChernClass_integralFactor, map_neg, LinearMap.neg_apply,
    coefficientClass_evaluate_basis_pair]

/-- Negating the coefficient vector preserves the actual type `(1,1)` condition. -/
theorem integralType_neg (p : PeriodDomain) (E : Fin 6 → ℤ)
    (hType : IsTypeOneOne (tangentForm p E)) : IsTypeOneOne (tangentForm p (-E)) := by
  simpa only [neg_one_zsmul] using integralType_zsmul p (-1) E hType

/-- The canonical factor for the negative form realizes the positive native class. -/
theorem firstChernClass_integralFactor_neg (p : PeriodDomain) (E : Fin 6 → ℤ)
    (hType : IsTypeOneOne (tangentForm p E)) :
    firstChernClass (integralFactor p (-E) (integralType_neg p E hType)) =
      coefficientClass p E := by
  rw [firstChernClass_integralFactor]
  change -(coefficientClassEquiv p (-E)) = coefficientClassEquiv p E
  rw [map_neg, neg_neg]

/-- Every integral type `(1,1)` coefficient class is the genuine first
Chern class of an explicitly constructed factor bundle. -/
theorem exists_factor_firstChernClass (p : PeriodDomain) (E : Fin 6 → ℤ)
    (hType : IsTypeOneOne (tangentForm p E)) :
    ∃ F : FactorOfAutomorphy p, firstChernClass F = coefficientClass p E :=
  ⟨integralFactor p (-E) (integralType_neg p E hType),
    firstChernClass_integralFactor_neg p E hType⟩

end Wikipedia.HopfProblem.PeriodTorusLineBundle.Chern
