import Wikipedia.HopfProblem.PeriodTorusCohomologyAlternatingBasic
import Wikipedia.HopfProblem.PeriodTorusTypeOneOneExterior
import Wikipedia.HopfProblem.PeriodTorusTypeOneOneTangent

/-!
# The source's integral alternating forms give actual second cohomology classes

The six coefficients `γu, γw, γδ, uw, uδ, wδ` are converted to actual
alternating maps using the proved exterior-dual pairing.  Native singular
evaluation then supplies a genuine integral second cohomology class.
Its value on every actual ordered product of positive period loops is
exactly the source coordinate form, and its six basis-pair values are
exactly the six prescribed integers.

The real comparison below concerns these genuine integral periods of
the actual tangent form.  It makes no Chern-class, cup-product, or
complex-orientation identification.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusCohomology

open FirstHurewicz SingularMayerVietoris SingularCohomologyFree
open PeriodTorusHigherHomology PeriodTorusHigherHomologyPontryagin
open PeriodTorusHigherHomologyExterior PeriodTorusTypeOneOne

/-- The source's six integer coefficients are all genuine alternating period forms. -/
def coefficientAlternatingEquiv :
    (Fin 6 → ℤ) ≃ₗ[ℤ] AlternatingMap ℤ Lattice ℤ (Fin 2) :=
  (integralExteriorForm.trans (dualPairingEquiv 2)).trans
    exteriorPower.alternatingMapLinearEquiv.symm

/-- The alternating map has exactly the prescribed bilinear values. -/
theorem coefficientAlternatingEquiv_apply (E : Fin 6 → ℤ) (x y : Lattice) :
    coefficientAlternatingEquiv E ![x, y] = coordinateForm E x y := by
  change exteriorPower.alternatingMapLinearEquiv.symm
    (dualPairingEquiv 2 (integralExteriorForm E)) ![x, y] = _
  rw [exteriorPower.alternatingMapLinearEquiv_symm_apply]
  exact integralExteriorForm_pairing E x y

theorem coefficientAlternatingEquiv_apply_family (E : Fin 6 → ℤ) (v : Fin 2 → Lattice) :
    coefficientAlternatingEquiv E v = coordinateForm E (v 0) (v 1) := by
  have hv : v = ![v 0, v 1] := by
    funext i
    fin_cases i <;> rfl
  rw [hv, coefficientAlternatingEquiv_apply]
  rfl

/-- The native integral second cohomology is exactly the six-coefficient module. -/
def coefficientClassEquiv (p : PeriodDomain) :
    (Fin 6 → ℤ) ≃ₗ[ℤ] SingularCohomology p.Torus 2 :=
  coefficientAlternatingEquiv.trans (cohomologyAlternatingEquiv p).symm

/-- The actual singular-cohomology class with the prescribed integral alternating periods. -/
def coefficientClass (p : PeriodDomain) (E : Fin 6 → ℤ) : SingularCohomology p.Torus 2 :=
  coefficientClassEquiv p E

@[simp] theorem coefficientClass_asAlternating (p : PeriodDomain) (E : Fin 6 → ℤ) :
    coefficientClass p E = alternatingClass p (coefficientAlternatingEquiv E) := rfl

/-- Evaluation on every actual homology class uses the genuine exterior-dual form. -/
theorem coefficientClass_evaluate (p : PeriodDomain) (E : Fin 6 → ℤ)
    (z : SingularHomology p.Torus 2) :
    singularEvaluation p.Torus 2 (coefficientClass p E) z =
      dualPairingEquiv 2 (integralExteriorForm E) (periodTorusH2ExteriorEquiv p z) := by
  rw [coefficientClass_asAlternating, alternatingClass_evaluate]
  change exteriorPower.alternatingMapLinearEquiv
    (exteriorPower.alternatingMapLinearEquiv.symm
      (dualPairingEquiv 2 (integralExteriorForm E))) (periodTorusH2ExteriorEquiv p z) = _
  rw [LinearEquiv.apply_symm_apply]

/-- The values are exact integers on actual products of the original positive period loops. -/
theorem coefficientClass_evaluate_periodLoops (p : PeriodDomain) (E : Fin 6 → ℤ)
    (x y : Lattice) :
    singularEvaluation p.Torus 2 (coefficientClass p E)
      (product11 p.Torus (loopHomologyClass (p.periodLoop x))
        (loopHomologyClass (p.periodLoop y))) = coordinateForm E x y := by
  rw [coefficientClass_asAlternating, alternatingClass_evaluate_periodLoops,
    coefficientAlternatingEquiv_apply]

/-- Each of the six coefficients is exactly evaluation on its actual named period-pair cycle. -/
theorem coefficientClass_evaluate_basis_pair (p : PeriodDomain) (E : Fin 6 → ℤ) (k : Fin 6) :
    singularEvaluation p.Torus 2 (coefficientClass p E)
      (product11 p.Torus
        (loopHomologyClass (p.periodLoop (Pi.single (coefficientPair k).1 1)))
        (loopHomologyClass (p.periodLoop (Pi.single (coefficientPair k).2 1)))) = E k := by
  rw [coefficientClass_evaluate_periodLoops]
  exact coordinateForm_basis_pair E k

/-- Even only the six named actual cycles uniquely determine the constructed native class. -/
theorem coefficientClass_unique_of_basis_pairs (p : PeriodDomain) (E : Fin 6 → ℤ)
    (a : SingularCohomology p.Torus 2)
    (ha : ∀ k : Fin 6, singularEvaluation p.Torus 2 a
      (product11 p.Torus
        (loopHomologyClass (p.periodLoop (Pi.single (coefficientPair k).1 1)))
        (loopHomologyClass (p.periodLoop (Pi.single (coefficientPair k).2 1)))) = E k) :
    a = coefficientClass p E := by
  obtain ⟨E', rfl⟩ := (coefficientClassEquiv p).surjective a
  have hE : E' = E := by
    funext k
    have hk := ha k
    change singularEvaluation p.Torus 2 (coefficientClass p E') _ = E k at hk
    rw [coefficientClass_evaluate_basis_pair] at hk
    exact hk
  rw [hE]
  rfl

/-- There is an actual, uniquely determined integral class for every six-coefficient form. -/
theorem existsUnique_coefficientClass (p : PeriodDomain) (E : Fin 6 → ℤ) :
    ∃! a : SingularCohomology p.Torus 2, ∀ k : Fin 6,
      singularEvaluation p.Torus 2 a
        (product11 p.Torus
          (loopHomologyClass (p.periodLoop (Pi.single (coefficientPair k).1 1)))
          (loopHomologyClass (p.periodLoop (Pi.single (coefficientPair k).2 1)))) = E k :=
  ⟨coefficientClass p E, coefficientClass_evaluate_basis_pair p E,
    fun a ha => coefficientClass_unique_of_basis_pairs p E a ha⟩

/-- The native class has precisely the integer periods of the actual real tangent form. -/
theorem coefficientClass_real_periods (p : PeriodDomain) (E : Fin 6 → ℤ) (x y : Lattice) :
    (singularEvaluation p.Torus 2 (coefficientClass p E)
      (product11 p.Torus (loopHomologyClass (p.periodLoop x))
        (loopHomologyClass (p.periodLoop y))) : ℝ) =
      tangentForm p E (periodEquiv p (fun i => (x i : ℝ)))
        (periodEquiv p (fun i => (y i : ℝ))) := by
  rw [coefficientClass_evaluate_periodLoops, tangentForm_integer_periods]

@[simp] theorem coefficientClass_add (p : PeriodDomain) (E F : Fin 6 → ℤ) :
    coefficientClass p (E + F) = coefficientClass p E + coefficientClass p F :=
  map_add (coefficientClassEquiv p) E F

@[simp] theorem coefficientClass_smul (p : PeriodDomain) (r : ℤ) (E : Fin 6 → ℤ) :
    coefficientClass p (r • E) = r • coefficientClass p E :=
  map_zsmul (coefficientClassEquiv p) r E

theorem coefficientClass_injective (p : PeriodDomain) : Function.Injective (coefficientClass p) :=
  (coefficientClassEquiv p).injective

end Wikipedia.HopfProblem.PeriodTorusCohomology
