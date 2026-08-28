import Wikipedia.HopfProblem.PeriodTorusCohomologyAlternatingCoordinates
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyMarkingFullPeriod

/-!
# Native integral second cohomology for arbitrary full period matrices

Every full period torus has the proved free integral homology and the
exterior-square marking by its actual positive period loops.  Canonical
singular-cochain evaluation therefore identifies its native second
cohomology with all integral alternating forms on the original four
integer coordinates, without normalizing the period matrix.

The inverse and the six-coefficient description preserve evaluation on
actual ordered products of period loops.  No cup-product, Chern-class,
or complex-orientation comparison is asserted here.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusCohomology

open FirstHurewicz SingularMayerVietoris SingularCohomologyFree
open PeriodTorusHigherHomology PeriodTorusHigherHomologyPontryagin
open PeriodTorusHigherHomologyExterior PeriodTorusTypeOneOne

/-- Native evaluation for every full period torus, using its proved actual homology freeness. -/
def fullEvaluationEquiv (q : FullPeriodMatrix) (n : ℕ) :
    SingularCohomology q.Torus n ≃ₗ[ℤ] Module.Dual ℤ (SingularHomology q.Torus n) := by
  letI (k : ℕ) : Module.Projective ℤ (SingularHomology q.Torus k) := by
    let := q.singularHomology_free k
    infer_instance
  exact singularEvaluationEquiv q.Torus n

@[simp] theorem fullEvaluationEquiv_apply (q : FullPeriodMatrix) (n : ℕ)
    (a : SingularCohomology q.Torus n) :
    fullEvaluationEquiv q n a = singularEvaluation q.Torus n a := rfl

/-- Actual second integral cohomology of any full period torus as alternating period forms. -/
def fullCohomologyAlternatingEquiv (q : FullPeriodMatrix) :
    SingularCohomology q.Torus 2 ≃ₗ[ℤ] AlternatingMap ℤ Lattice ℤ (Fin 2) :=
  (fullEvaluationEquiv q 2).trans
    ((fullPeriodTorusH2ExteriorEquiv q).symm.dualMap.trans
      exteriorPower.alternatingMapLinearEquiv.symm)

/-- The alternating form is genuine evaluation on the actual full-period exterior marking. -/
theorem fullCohomologyAlternatingEquiv_apply_exterior (q : FullPeriodMatrix)
    (a : SingularCohomology q.Torus 2) (v : Fin 2 → Lattice) :
    fullCohomologyAlternatingEquiv q a v =
      singularEvaluation q.Torus 2 a
        ((fullPeriodTorusH2ExteriorEquiv q).symm (exteriorPower.ιMulti ℤ 2 v)) := by
  simp only [fullCohomologyAlternatingEquiv, LinearEquiv.trans_apply,
    exteriorPower.alternatingMapLinearEquiv_symm_apply,
    LinearMap.compAlternatingMap_apply, LinearEquiv.dualMap_apply, fullEvaluationEquiv_apply]

/-- Literal evaluation on the ordered product of the original positive full-period loops. -/
theorem fullCohomologyAlternatingEquiv_apply (q : FullPeriodMatrix)
    (a : SingularCohomology q.Torus 2) (v : Fin 2 → Lattice) :
    fullCohomologyAlternatingEquiv q a v =
      singularEvaluation q.Torus 2 a
        (product11 q.Torus
          (loopHomologyClass (q.periodLoop
            (FullPeriodMatrix.integerCoordinatesEquiv.symm (v 0))))
          (loopHomologyClass (q.periodLoop
            (FullPeriodMatrix.integerCoordinatesEquiv.symm (v 1))))) := by
  rw [fullCohomologyAlternatingEquiv_apply_exterior,
    fullPeriodTorusH2ExteriorEquiv_symm_ιMulti]

/-- The actual native cohomology class of an integral alternating form on any full period torus. -/
def fullAlternatingClass (q : FullPeriodMatrix) (B : AlternatingMap ℤ Lattice ℤ (Fin 2)) :
    SingularCohomology q.Torus 2 :=
  (fullCohomologyAlternatingEquiv q).symm B

@[simp] theorem fullCohomologyAlternatingEquiv_fullAlternatingClass (q : FullPeriodMatrix)
    (B : AlternatingMap ℤ Lattice ℤ (Fin 2)) :
    fullCohomologyAlternatingEquiv q (fullAlternatingClass q B) = B :=
  (fullCohomologyAlternatingEquiv q).apply_symm_apply B

@[simp] theorem fullAlternatingClass_fullCohomologyAlternatingEquiv (q : FullPeriodMatrix)
    (a : SingularCohomology q.Torus 2) :
    fullAlternatingClass q (fullCohomologyAlternatingEquiv q a) = a :=
  (fullCohomologyAlternatingEquiv q).symm_apply_apply a

/-- Evaluation on every actual homology class agrees with the exterior lift of the form. -/
theorem fullAlternatingClass_evaluate (q : FullPeriodMatrix)
    (B : AlternatingMap ℤ Lattice ℤ (Fin 2)) (z : SingularHomology q.Torus 2) :
    singularEvaluation q.Torus 2 (fullAlternatingClass q B) z =
      exteriorPower.alternatingMapLinearEquiv B (fullPeriodTorusH2ExteriorEquiv q z) := by
  change fullEvaluationEquiv q 2 (fullAlternatingClass q B) z = _
  simp only [fullAlternatingClass, fullCohomologyAlternatingEquiv,
    LinearEquiv.symm_trans_apply, LinearEquiv.dualMap_symm, LinearEquiv.symm_symm,
    LinearEquiv.apply_symm_apply, LinearEquiv.dualMap_apply]

theorem fullAlternatingClass_evaluate_exterior (q : FullPeriodMatrix)
    (B : AlternatingMap ℤ Lattice ℤ (Fin 2)) (v : Fin 2 → Lattice) :
    singularEvaluation q.Torus 2 (fullAlternatingClass q B)
      ((fullPeriodTorusH2ExteriorEquiv q).symm (exteriorPower.ιMulti ℤ 2 v)) = B v := by
  rw [fullAlternatingClass_evaluate, LinearEquiv.apply_symm_apply,
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]

/-- Exact integer evaluation on the genuine ordered product of two positive period loops. -/
theorem fullAlternatingClass_evaluate_periodLoops (q : FullPeriodMatrix)
    (B : AlternatingMap ℤ Lattice ℤ (Fin 2)) (x y : Lattice) :
    singularEvaluation q.Torus 2 (fullAlternatingClass q B)
      (product11 q.Torus
        (loopHomologyClass (q.periodLoop (FullPeriodMatrix.integerCoordinatesEquiv.symm x)))
        (loopHomologyClass (q.periodLoop (FullPeriodMatrix.integerCoordinatesEquiv.symm y)))) =
      B ![x, y] := by
  have h := fullAlternatingClass_evaluate_exterior q B ![x, y]
  rw [fullPeriodTorusH2ExteriorEquiv_symm_ιMulti] at h
  exact h

/-- Actual products of positive full-period loops detect every native second cohomology class. -/
theorem fullCohomology_ext_periodLoops (q : FullPeriodMatrix)
    {a b : SingularCohomology q.Torus 2}
    (h : ∀ x y : Lattice,
      singularEvaluation q.Torus 2 a
        (product11 q.Torus
          (loopHomologyClass (q.periodLoop (FullPeriodMatrix.integerCoordinatesEquiv.symm x)))
          (loopHomologyClass (q.periodLoop (FullPeriodMatrix.integerCoordinatesEquiv.symm y)))) =
      singularEvaluation q.Torus 2 b
        (product11 q.Torus
          (loopHomologyClass (q.periodLoop (FullPeriodMatrix.integerCoordinatesEquiv.symm x)))
          (loopHomologyClass (q.periodLoop (FullPeriodMatrix.integerCoordinatesEquiv.symm y))))) :
    a = b := by
  apply (fullCohomologyAlternatingEquiv q).injective
  apply AlternatingMap.ext
  intro v
  rw [fullCohomologyAlternatingEquiv_apply, fullCohomologyAlternatingEquiv_apply]
  exact h (v 0) (v 1)

theorem fullAlternatingClass_unique (q : FullPeriodMatrix)
    (B : AlternatingMap ℤ Lattice ℤ (Fin 2)) (a : SingularCohomology q.Torus 2)
    (h : ∀ x y : Lattice,
      singularEvaluation q.Torus 2 a
        (product11 q.Torus
          (loopHomologyClass (q.periodLoop (FullPeriodMatrix.integerCoordinatesEquiv.symm x)))
          (loopHomologyClass (q.periodLoop (FullPeriodMatrix.integerCoordinatesEquiv.symm y)))) =
      B ![x, y]) : a = fullAlternatingClass q B := by
  apply fullCohomology_ext_periodLoops q
  intro x y
  rw [fullAlternatingClass_evaluate_periodLoops]
  exact h x y

/-- Every integral alternating form has exactly one actual class with these loop evaluations. -/
theorem existsUnique_fullAlternatingClass (q : FullPeriodMatrix)
    (B : AlternatingMap ℤ Lattice ℤ (Fin 2)) :
    ∃! a : SingularCohomology q.Torus 2, ∀ x y : Lattice,
      singularEvaluation q.Torus 2 a
        (product11 q.Torus
          (loopHomologyClass (q.periodLoop (FullPeriodMatrix.integerCoordinatesEquiv.symm x)))
          (loopHomologyClass (q.periodLoop (FullPeriodMatrix.integerCoordinatesEquiv.symm y)))) =
      B ![x, y] :=
  ⟨fullAlternatingClass q B, fullAlternatingClass_evaluate_periodLoops q B,
    fun a h => fullAlternatingClass_unique q B a h⟩

/-- All native classes, not only a designated family, arise from alternating forms. -/
theorem fullAlternatingClass_bijective (q : FullPeriodMatrix) :
    Function.Bijective (fullAlternatingClass q) :=
  (fullCohomologyAlternatingEquiv q).symm.bijective

/-- The six integral coefficients parametrize all native second cohomology classes. -/
def fullCoefficientClassEquiv (q : FullPeriodMatrix) :
    (Fin 6 → ℤ) ≃ₗ[ℤ] SingularCohomology q.Torus 2 :=
  coefficientAlternatingEquiv.trans (fullCohomologyAlternatingEquiv q).symm

/-- The actual full-period cohomology class with the prescribed integer alternating periods. -/
def fullCoefficientClass (q : FullPeriodMatrix) (E : Fin 6 → ℤ) :
    SingularCohomology q.Torus 2 :=
  fullCoefficientClassEquiv q E

@[simp] theorem fullCoefficientClass_asAlternating (q : FullPeriodMatrix) (E : Fin 6 → ℤ) :
    fullCoefficientClass q E = fullAlternatingClass q (coefficientAlternatingEquiv E) := rfl

/-- Evaluation on every native homology class uses the genuine exterior-dual period form. -/
theorem fullCoefficientClass_evaluate (q : FullPeriodMatrix) (E : Fin 6 → ℤ)
    (z : SingularHomology q.Torus 2) :
    singularEvaluation q.Torus 2 (fullCoefficientClass q E) z =
      dualPairingEquiv 2 (integralExteriorForm E) (fullPeriodTorusH2ExteriorEquiv q z) := by
  rw [fullCoefficientClass_asAlternating, fullAlternatingClass_evaluate]
  change exteriorPower.alternatingMapLinearEquiv
    (exteriorPower.alternatingMapLinearEquiv.symm
      (dualPairingEquiv 2 (integralExteriorForm E))) (fullPeriodTorusH2ExteriorEquiv q z) = _
  rw [LinearEquiv.apply_symm_apply]

/-- The actual ordered loop products have exactly the prescribed integer bilinear periods. -/
theorem fullCoefficientClass_evaluate_periodLoops (q : FullPeriodMatrix) (E : Fin 6 → ℤ)
    (x y : Lattice) :
    singularEvaluation q.Torus 2 (fullCoefficientClass q E)
      (product11 q.Torus
        (loopHomologyClass (q.periodLoop (FullPeriodMatrix.integerCoordinatesEquiv.symm x)))
        (loopHomologyClass (q.periodLoop (FullPeriodMatrix.integerCoordinatesEquiv.symm y)))) =
      coordinateForm E x y := by
  rw [fullCoefficientClass_asAlternating, fullAlternatingClass_evaluate_periodLoops,
    coefficientAlternatingEquiv_apply]

/-- Each coefficient is evaluation on its actual named ordered pair of full-period loops. -/
theorem fullCoefficientClass_evaluate_basis_pair (q : FullPeriodMatrix)
    (E : Fin 6 → ℤ) (k : Fin 6) :
    singularEvaluation q.Torus 2 (fullCoefficientClass q E)
      (product11 q.Torus
        (loopHomologyClass (q.periodLoop (FullPeriodMatrix.integerCoordinatesEquiv.symm
          (Pi.single (coefficientPair k).1 1))))
        (loopHomologyClass (q.periodLoop (FullPeriodMatrix.integerCoordinatesEquiv.symm
          (Pi.single (coefficientPair k).2 1))))) = E k := by
  rw [fullCoefficientClass_evaluate_periodLoops]
  exact coordinateForm_basis_pair E k

/-- The six actual named cycles uniquely determine the native integral cohomology class. -/
theorem fullCoefficientClass_unique_of_basis_pairs (q : FullPeriodMatrix) (E : Fin 6 → ℤ)
    (a : SingularCohomology q.Torus 2)
    (ha : ∀ k : Fin 6, singularEvaluation q.Torus 2 a
      (product11 q.Torus
        (loopHomologyClass (q.periodLoop (FullPeriodMatrix.integerCoordinatesEquiv.symm
          (Pi.single (coefficientPair k).1 1))))
        (loopHomologyClass (q.periodLoop (FullPeriodMatrix.integerCoordinatesEquiv.symm
          (Pi.single (coefficientPair k).2 1))))) = E k) :
    a = fullCoefficientClass q E := by
  obtain ⟨E', rfl⟩ := (fullCoefficientClassEquiv q).surjective a
  have hE : E' = E := by
    funext k
    have hk := ha k
    change singularEvaluation q.Torus 2 (fullCoefficientClass q E') _ = E k at hk
    rw [fullCoefficientClass_evaluate_basis_pair] at hk
    exact hk
  rw [hE]
  rfl

/-- Every six-coefficient form gives exactly one actual class with these six integer periods. -/
theorem existsUnique_fullCoefficientClass (q : FullPeriodMatrix) (E : Fin 6 → ℤ) :
    ∃! a : SingularCohomology q.Torus 2, ∀ k : Fin 6,
      singularEvaluation q.Torus 2 a
        (product11 q.Torus
          (loopHomologyClass (q.periodLoop (FullPeriodMatrix.integerCoordinatesEquiv.symm
            (Pi.single (coefficientPair k).1 1))))
          (loopHomologyClass (q.periodLoop (FullPeriodMatrix.integerCoordinatesEquiv.symm
            (Pi.single (coefficientPair k).2 1))))) = E k :=
  ⟨fullCoefficientClass q E, fullCoefficientClass_evaluate_basis_pair q E,
    fun a ha => fullCoefficientClass_unique_of_basis_pairs q E a ha⟩

@[simp] theorem fullCoefficientClass_add (q : FullPeriodMatrix) (E F : Fin 6 → ℤ) :
    fullCoefficientClass q (E + F) = fullCoefficientClass q E + fullCoefficientClass q F :=
  map_add (fullCoefficientClassEquiv q) E F

@[simp] theorem fullCoefficientClass_smul (q : FullPeriodMatrix) (r : ℤ) (E : Fin 6 → ℤ) :
    fullCoefficientClass q (r • E) = r • fullCoefficientClass q E :=
  map_zsmul (fullCoefficientClassEquiv q) r E

theorem fullCoefficientClass_injective (q : FullPeriodMatrix) :
    Function.Injective (fullCoefficientClass q) :=
  (fullCoefficientClassEquiv q).injective

/-- Every native integral second cohomology class has exactly one six-coefficient description. -/
theorem fullCoefficientClass_bijective (q : FullPeriodMatrix) :
    Function.Bijective (fullCoefficientClass q) :=
  (fullCoefficientClassEquiv q).bijective

end Wikipedia.HopfProblem.PeriodTorusCohomology
