import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationLogCocycle
import Wikipedia.HopfProblem.PeriodTorusTypeOneOneIntegralCompleteness

/-!
# Actual integer coefficients of the logarithmic commutator

Every alternating integer pairing on the actual period lattice is recovered
from its six ordered basis values. The coefficients of a factor of automorphy
are extracted from its already proved logarithmic commutator, not assumed.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassification

open PeriodTorusAppellHumbert PeriodTorusTypeOneOne

def integerFormCoefficients (B : LinearMap.BilinForm ℤ (Fin 4 → ℤ)) : Fin 6 → ℤ :=
  fun k => B (Pi.single (coefficientPair k).1 1) (Pi.single (coefficientPair k).2 1)

theorem coordinateForm_integerFormCoefficients (B : LinearMap.BilinForm ℤ (Fin 4 → ℤ))
    (hB : B.IsAlt) : coordinateForm (integerFormCoefficients B) = B := by
  have hskew (x y : Fin 4 → ℤ) : B x y = -B y x := by
    have h := hB (x + y)
    simp only [map_add, LinearMap.add_apply] at h
    linear_combination h - hB x - hB y
  have hlt (i j : Fin 4) (hij : i < j) :
      coordinateForm (integerFormCoefficients B) (Pi.single i 1) (Pi.single j 1) =
        B (Pi.single i 1) (Pi.single j 1) := by
    obtain ⟨k, hk⟩ := coefficientPair_covers_lt i j hij
    have h := coordinateForm_basis_pair (integerFormCoefficients B) k
    simpa only [integerFormCoefficients, hk] using h
  apply LinearMap.BilinForm.ext_basis (Pi.basisFun ℤ (Fin 4))
  intro i j
  simp only [Pi.basisFun_apply]
  rcases lt_trichotomy i j with hij | hij | hij
  · exact hlt i j hij
  · subst j
    exact (coordinateForm_self _ _).trans (hB _).symm
  · rw [coordinateForm_swap, hskew, hlt j i hij]

/-- The actual lattice alternating pairing in the marked integer coordinates. -/
def factorCoordinateForm {p : PeriodDomain} (F : FactorOfAutomorphy p) :
    LinearMap.BilinForm ℤ (Fin 4 → ℤ) :=
  (factorLogAlternatingForm F).compl₁₂
    p.periodLatticeEquiv.toIntLinearEquiv.toLinearMap
    p.periodLatticeEquiv.toIntLinearEquiv.toLinearMap

@[simp]
theorem factorCoordinateForm_apply {p : PeriodDomain} (F : FactorOfAutomorphy p)
    (x y : Fin 4 → ℤ) :
    factorCoordinateForm F x y = factorLogAlternatingForm F
      (p.periodLatticeEquiv x) (p.periodLatticeEquiv y) := rfl

theorem factorCoordinateForm_isAlt {p : PeriodDomain} (F : FactorOfAutomorphy p) :
    (factorCoordinateForm F).IsAlt :=
  fun x => factorLogAlternatingForm_isAlt F (p.periodLatticeEquiv x)

/-- Six integer coefficients extracted from the genuine factor logarithms. -/
def factorIntegralCoefficients {p : PeriodDomain} (F : FactorOfAutomorphy p) : Fin 6 → ℤ :=
  integerFormCoefficients (factorCoordinateForm F)

theorem factorIntegralCoefficients_spec {p : PeriodDomain} (F : FactorOfAutomorphy p)
    (l m : p.lattice) :
    coordinateForm (factorIntegralCoefficients F) (p.latticeEquiv l) (p.latticeEquiv m) =
      factorLogAlternatingForm F l m := by
  rw [factorIntegralCoefficients,
    coordinateForm_integerFormCoefficients _ (factorCoordinateForm_isAlt F),
    factorCoordinateForm_apply]
  simp only [PeriodDomain.latticeEquiv, AddEquiv.apply_symm_apply]

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassification
