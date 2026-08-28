import Wikipedia.HopfProblem.PeriodTorusCohomologyAlternatingFullPeriodComparison
import Wikipedia.HopfProblem.PeriodTorusCohomologyAlternatingEta

/-!
# The distinguished native integral class in full-period coordinates

In the raw `[I | Z]` marking the distinguished class has coefficients
`(0,0,-1,-6,0,0)`.  Its evaluation on the actual ordered positive
coordinate loops `0,3` is minus one, proving nonvanishing and integral
primitivity for every full period matrix.

The actual comparison biholomorphism carries this class to the ordinary
eta class by native cohomology pullback.  Its inverse gives the reverse
comparison.  The block swap and all signs are retained; no Chern-class,
cup-product, or complex-orientation identification is asserted.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusCohomology

open FirstHurewicz SingularMayerVietoris SingularCohomologyFree
open PeriodTorusHigherHomology PeriodTorusHigherHomologyPontryagin
open PeriodTorusTypeOneOne SpecialPeriods

/-- The distinguished genuine integral class in the raw full-period marking. -/
def fullEtaClass (q : FullPeriodMatrix) : SingularCohomology q.Torus 2 :=
  fullCoefficientClass q ![0, 0, -1, -6, 0, 0]

/-- Its exact integer evaluation on actual ordered products of positive raw period loops. -/
theorem fullEtaClass_evaluate_periodLoops (q : FullPeriodMatrix) (x y : Lattice) :
    singularEvaluation q.Torus 2 (fullEtaClass q)
      (product11 q.Torus
        (loopHomologyClass (q.periodLoop (FullPeriodMatrix.integerCoordinatesEquiv.symm x)))
        (loopHomologyClass (q.periodLoop (FullPeriodMatrix.integerCoordinatesEquiv.symm y)))) =
      -(x 0 * y 3 - x 3 * y 0) - 6 * (x 1 * y 2 - x 2 * y 1) := by
  rw [fullEtaClass, fullCoefficientClass_evaluate_periodLoops]
  simp only [coordinateForm_apply, coordinateValue,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    zero_mul, add_zero, zero_add]
  ring

/-- All six actual raw coordinate-pair cycles have the prescribed integral values. -/
theorem fullEtaClass_evaluate_basis_pair (q : FullPeriodMatrix) (k : Fin 6) :
    singularEvaluation q.Torus 2 (fullEtaClass q)
      (product11 q.Torus
        (loopHomologyClass (q.periodLoop (FullPeriodMatrix.integerCoordinatesEquiv.symm
          (Pi.single (coefficientPair k).1 1))))
        (loopHomologyClass (q.periodLoop (FullPeriodMatrix.integerCoordinatesEquiv.symm
          (Pi.single (coefficientPair k).2 1))))) =
      (![0, 0, -1, -6, 0, 0] : Fin 6 → ℤ) k :=
  fullCoefficientClass_evaluate_basis_pair q ![0, 0, -1, -6, 0, 0] k

/-- The actual ordered product of positive raw coordinate loops zero and three. -/
def fullEtaPairCycle (q : FullPeriodMatrix) : SingularHomology q.Torus 2 :=
  product11 q.Torus
    (loopHomologyClass (q.periodLoop
      (FullPeriodMatrix.integerCoordinatesEquiv.symm (Pi.single 0 1))))
    (loopHomologyClass (q.periodLoop
      (FullPeriodMatrix.integerCoordinatesEquiv.symm (Pi.single 3 1))))

/-- Evaluation on the genuine raw zero-three period cycle is an integral linear functional. -/
def fullEtaEvaluation (q : FullPeriodMatrix) : SingularCohomology q.Torus 2 →ₗ[ℤ] ℤ :=
  (singularEvaluation q.Torus 2).flip (fullEtaPairCycle q)

theorem fullEtaEvaluation_apply (q : FullPeriodMatrix) (a : SingularCohomology q.Torus 2) :
    fullEtaEvaluation q a = singularEvaluation q.Torus 2 a (fullEtaPairCycle q) := rfl

@[simp] theorem fullEtaEvaluation_fullEtaClass (q : FullPeriodMatrix) :
    fullEtaEvaluation q (fullEtaClass q) = -1 := by
  have h := fullEtaClass_evaluate_basis_pair q (2 : Fin 6)
  simpa only [fullEtaEvaluation_apply, fullEtaPairCycle, coefficientPair,
    Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] using h

/-- The primitive normalization is a literal evaluation on two actual positive period loops. -/
theorem fullEtaClass_evaluate_zero_three (q : FullPeriodMatrix) :
    singularEvaluation q.Torus 2 (fullEtaClass q)
      (product11 q.Torus
        (loopHomologyClass (q.periodLoop
          (FullPeriodMatrix.integerCoordinatesEquiv.symm (Pi.single 0 1))))
        (loopHomologyClass (q.periodLoop
          (FullPeriodMatrix.integerCoordinatesEquiv.symm (Pi.single 3 1))))) = -1 :=
  fullEtaEvaluation_fullEtaClass q

/-- The distinguished full-period class is nonzero, witnessed by an actual period cycle. -/
theorem fullEtaClass_ne_zero (q : FullPeriodMatrix) : fullEtaClass q ≠ 0 := by
  intro h
  have he := fullEtaEvaluation_fullEtaClass q
  rw [h, map_zero] at he
  norm_num at he

/-- No nonunit integer divides the genuine full-period class. -/
theorem fullEtaClass_primitive (q : FullPeriodMatrix) (r : ℤ)
    (a : SingularCohomology q.Torus 2) (ha : r • a = fullEtaClass q) : IsUnit r := by
  have he := congrArg (fullEtaEvaluation q) ha
  rw [map_zsmul, fullEtaEvaluation_fullEtaClass, zsmul_eq_mul, Int.cast_id] at he
  refine isUnit_iff_dvd_one.mpr ⟨-fullEtaEvaluation q a, ?_⟩
  rw [mul_neg, he]
  norm_num

/-- All integer multiples are distinct in actual native cohomology. -/
theorem fullEtaClass_zsmul_injective (q : FullPeriodMatrix) :
    Function.Injective (fun r : ℤ => r • fullEtaClass q) := by
  intro r s h
  have he := congrArg (fullEtaEvaluation q) h
  simpa using he

/-- The actual identity-induced comparison pulls the raw full-period class back to eta. -/
theorem fullEtaClass_pullback_comparison (p : PeriodDomain) (q : FullPeriodMatrix)
    (h : q.matrix = p.val.leftBlock) :
    singularCohomologyPullback (p.fullPeriodContinuousMap q h) 2 (fullEtaClass q) =
      etaClass p := by
  simpa [fullEtaClass, etaClass, periodRelationEta] using
    fullCoefficientClass_pullback_comparison_explicit p q h ![0, 0, -1, -6, 0, 0]

/-- The actual comparison cohomology equivalence preserves the distinguished geometric class. -/
theorem fullPeriodComparisonCohomologyEquiv_fullEtaClass (p : PeriodDomain)
    (q : FullPeriodMatrix) (h : q.matrix = p.val.leftBlock) :
    fullPeriodComparisonCohomologyEquiv p q h 2 (fullEtaClass q) = etaClass p := by
  rw [fullPeriodComparisonCohomologyEquiv_apply, fullEtaClass_pullback_comparison]

/-- The inverse genuine equivalence gives the same class in its raw full-period coordinates. -/
theorem fullPeriodComparisonCohomologyEquiv_symm_etaClass (p : PeriodDomain)
    (q : FullPeriodMatrix) (h : q.matrix = p.val.leftBlock) :
    (fullPeriodComparisonCohomologyEquiv p q h 2).symm (etaClass p) = fullEtaClass q := by
  apply (fullPeriodComparisonCohomologyEquiv p q h 2).injective
  rw [LinearEquiv.apply_symm_apply, fullPeriodComparisonCohomologyEquiv_fullEtaClass]

/-- Literal native pullback by the inverse biholomorphism sends ordinary eta to raw full eta. -/
theorem etaClass_pullback_fullPeriodComparison_symm (p : PeriodDomain)
    (q : FullPeriodMatrix) (h : q.matrix = p.val.leftBlock) :
    singularCohomologyPullback
        ((p.fullPeriodBiholomorph q h).toHomeomorph.symm : C(q.Torus, p.Torus)) 2 (etaClass p) =
      fullEtaClass q := by
  rw [← fullPeriodComparisonCohomologyEquiv_symm_apply,
    fullPeriodComparisonCohomologyEquiv_symm_etaClass]

end Wikipedia.HopfProblem.PeriodTorusCohomology
