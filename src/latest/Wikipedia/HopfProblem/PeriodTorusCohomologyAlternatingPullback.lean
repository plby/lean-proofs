import Wikipedia.HopfProblem.PeriodTorusCohomologyAlternatingCoordinates
import Wikipedia.HopfProblem.PeriodTorusCohomologyAlternatingNaturality

/-!
# Actual pullback of the source's six-coordinate integral classes

An integral lattice map pulls back the actual alternating form in its
six original coordinates.  Its coefficients are evaluated explicitly on
the images of the named lattice basis pairs.  The proved native
cohomology comparison then yields pullback equations for the genuine
period-change maps without assuming an action on cohomology.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusCohomology

open SingularMayerVietoris SingularCohomologyFree PeriodTorusHigherHomology
open PeriodTorusTypeOneOne

/-- Pullback of the actual source alternating form by an integral lattice map. -/
def coefficientPullback (A : Lattice →ₗ[ℤ] Lattice) (E : Fin 6 → ℤ) : Fin 6 → ℤ :=
  coefficientAlternatingEquiv.symm ((coefficientAlternatingEquiv E).compLinearMap A)

@[simp] theorem coefficientAlternatingEquiv_coefficientPullback
    (A : Lattice →ₗ[ℤ] Lattice) (E : Fin 6 → ℤ) :
    coefficientAlternatingEquiv (coefficientPullback A E) =
      (coefficientAlternatingEquiv E).compLinearMap A :=
  coefficientAlternatingEquiv.apply_symm_apply _

/-- Pullback really evaluates the original bilinear form on the images of both vectors. -/
theorem coefficientPullback_form (A : Lattice →ₗ[ℤ] Lattice) (E : Fin 6 → ℤ)
    (x y : Lattice) :
    coordinateForm (coefficientPullback A E) x y = coordinateForm E (A x) (A y) := by
  rw [← coefficientAlternatingEquiv_apply,
    coefficientAlternatingEquiv_coefficientPullback,
    AlternatingMap.compLinearMap_apply, coefficientAlternatingEquiv_apply_family]
  rfl

/-- Every new coefficient is the exact integer evaluation on its named transformed basis pair. -/
theorem coefficientPullback_apply (A : Lattice →ₗ[ℤ] Lattice) (E : Fin 6 → ℤ) (k : Fin 6) :
    coefficientPullback A E k =
      coordinateForm E (A (Pi.single (coefficientPair k).1 1))
        (A (Pi.single (coefficientPair k).2 1)) := by
  rw [← coordinateForm_basis_pair (coefficientPullback A E) k, coefficientPullback_form]

@[simp] theorem coefficientPullback_id (E : Fin 6 → ℤ) :
    coefficientPullback LinearMap.id E = E := by
  apply coefficientAlternatingEquiv.injective
  rw [coefficientAlternatingEquiv_coefficientPullback, AlternatingMap.compLinearMap_id]

/-- Pullback reverses the order of the actual lattice-map composition. -/
theorem coefficientPullback_comp (A B : Lattice →ₗ[ℤ] Lattice) (E : Fin 6 → ℤ) :
    coefficientPullback (A.comp B) E = coefficientPullback B (coefficientPullback A E) := by
  apply coefficientAlternatingEquiv.injective
  rw [coefficientAlternatingEquiv_coefficientPullback,
    coefficientAlternatingEquiv_coefficientPullback,
    coefficientAlternatingEquiv_coefficientPullback, AlternatingMap.compLinearMap_assoc]

theorem coefficientPullback_add (A : Lattice →ₗ[ℤ] Lattice) (E F : Fin 6 → ℤ) :
    coefficientPullback A (E + F) = coefficientPullback A E + coefficientPullback A F := by
  simp only [coefficientPullback, map_add, AlternatingMap.add_compLinearMap]

/-- A proved actual exterior-homology diagram gives actual pullback of the native source class. -/
theorem coefficientClass_pullback_of_exterior (p q : PeriodDomain)
    (f : C(p.Torus, q.Torus)) (A : Lattice →ₗ[ℤ] Lattice)
    (hA : ∀ z : SingularHomology p.Torus 2,
      periodTorusH2ExteriorEquiv q (singularHomologyMap f 2 z) =
        exteriorPower.map 2 A (periodTorusH2ExteriorEquiv p z)) (E : Fin 6 → ℤ) :
    singularCohomologyPullback f 2 (coefficientClass q E) =
      coefficientClass p (coefficientPullback A E) := by
  rw [coefficientClass_asAlternating, coefficientClass_asAlternating,
    coefficientAlternatingEquiv_coefficientPullback]
  exact alternatingClass_pullback_of_exterior p q f A hA _

/-- The first actual period-change pullback, in the source's integral coordinates. -/
theorem coefficientClass_pullback_step₁ (p : PeriodDomain) (E : Fin 6 → ℤ) :
    singularCohomologyPullback p.step₁ContinuousMap 2 (coefficientClass p.step₁ E) =
      coefficientClass p (coefficientPullback A₁.mulVecLin E) :=
  coefficientClass_pullback_of_exterior p p.step₁ p.step₁ContinuousMap A₁.mulVecLin
    (periodTorusH2ExteriorEquiv_step₁ p) E

/-- The second actual period-change pullback has its proved integer lattice action. -/
theorem coefficientClass_pullback_step₂ (p : PeriodDomain) (E : Fin 6 → ℤ) :
    singularCohomologyPullback p.step₂ContinuousMap 2 (coefficientClass p.step₂ E) =
      coefficientClass p (coefficientPullback A₂.mulVecLin E) :=
  coefficientClass_pullback_of_exterior p p.step₂ p.step₂ContinuousMap A₂.mulVecLin
    (periodTorusH2ExteriorEquiv_step₂ p) E

/-- The actual cusp period change acts by the actual unipotent lattice pullback. -/
theorem coefficientClass_pullback_step₀ (p : PeriodDomain) (E : Fin 6 → ℤ) :
    singularCohomologyPullback p.step₀ContinuousMap 2 (coefficientClass p.step₀ E) =
      coefficientClass p (coefficientPullback M₀.mulVecLin E) :=
  coefficientClass_pullback_of_exterior p p.step₀ p.step₀ContinuousMap M₀.mulVecLin
    (periodTorusH2ExteriorEquiv_step₀ p) E

end Wikipedia.HopfProblem.PeriodTorusCohomology
