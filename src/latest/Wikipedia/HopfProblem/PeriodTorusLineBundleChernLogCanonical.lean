import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationLogCanonical

/-!
# An explicit unwrapped logarithm for the canonical Appell--Humbert factor

The actual canonical semicharacter is the exponential of the marked
quadratic expression.  Adding that unwrapped phase to the Hermitian
exponent gives a holomorphic logarithm of the actual factor.  Its positive
translation defect is the explicit upper-triangular integral cocycle.
This fixes the logarithmic sign without asserting a Chern-class comparison.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleChernLog

open Complex PeriodTorusAppellHumbert PeriodTorusTypeOneOne
open PeriodTorusLineBundleClassification
open scoped BigOperators ContDiff

/-- The unwrapped quadratic phase together with the genuine Hermitian exponent. -/
def canonicalLog (p : PeriodDomain) (E : Fin 6 → ℤ)
    (hType : IsTypeOneOne (tangentForm p E)) (l : p.lattice) (z : ComplexPlane₂) : ℂ :=
  appellHumbertExponent (integralHermitian p E hType) l z +
    (Real.pi : ℂ) * I * (coordinateQuadratic E (p.latticeEquiv l) : ℂ)

/-- The original positive upper-triangular integer pairing, on the actual period lattice. -/
def canonicalIntegerCocycle (p : PeriodDomain) (E : Fin 6 → ℤ)
    (l m : p.lattice) : ℤ :=
  ∑ k : Fin 6, E k * (p.latticeEquiv l) (coefficientPair k).1 *
    (p.latticeEquiv m) (coefficientPair k).2

/-- Exponentiation recovers exactly the actual canonical factor. -/
theorem canonicalLog_exp (p : PeriodDomain) (E : Fin 6 → ℤ)
    (hType : IsTypeOneOne (tangentForm p E)) (l : p.lattice) (z : ComplexPlane₂) :
    Complex.exp (canonicalLog p E hType l z) =
      ((integralFactor p E hType).factor l z : ℂ) := by
  rw [canonicalLog, Complex.exp_add, integralFactor_coe]
  exact mul_comm _ _

/-- The explicit logarithm is normalized at the zero lattice translation. -/
@[simp] theorem canonicalLog_zero (p : PeriodDomain) (E : Fin 6 → ℤ)
    (hType : IsTypeOneOne (tangentForm p E)) (z : ComplexPlane₂) :
    canonicalLog p E hType 0 z = 0 := by
  simp [canonicalLog, appellHumbertExponent]

theorem canonicalLog_holomorphic (p : PeriodDomain) (E : Fin 6 → ℤ)
    (hType : IsTypeOneOne (tangentForm p E)) (l : p.lattice) :
    ContDiff ℂ ω (canonicalLog p E hType l) :=
  (appellHumbertExponent_holomorphic (integralHermitian p E hType) l).add contDiff_const

private theorem coordinateQuadratic_add_form (E : Fin 6 → ℤ) (x y : Lattice) :
    coordinateQuadratic E (x + y) - coordinateQuadratic E x - coordinateQuadratic E y +
      coordinateForm E x y =
        2 * ∑ k : Fin 6, E k * x (coefficientPair k).1 * y (coefficientPair k).2 := by
  simp [Fin.sum_univ_succ, coefficientPair, coordinateQuadratic,
    coordinateForm_apply, coordinateValue, Pi.add_apply]
  ring

/-- The unwrapped logarithm has precisely the positive upper-triangular integer defect. -/
theorem canonicalLog_hasIntegerLogDefect (p : PeriodDomain) (E : Fin 6 → ℤ)
    (hType : IsTypeOneOne (tangentForm p E)) :
    HasIntegerLogDefect p (canonicalLog p E hType) (canonicalIntegerCocycle p E) := by
  intro l m z
  have hHerm := appellHumbertExponent_cocycle (integralHermitian p E hType)
    (integralHermitian_isHermitian p E hType) (l : ComplexPlane₂) (m : ComplexPlane₂) z
  rw [integralHermitian_lattice_im, Complex.ofReal_intCast] at hHerm
  have hquad : coordinateQuadratic E (p.latticeEquiv l + p.latticeEquiv m) -
      coordinateQuadratic E (p.latticeEquiv l) - coordinateQuadratic E (p.latticeEquiv m) +
        coordinateForm E (p.latticeEquiv l) (p.latticeEquiv m) =
          2 * canonicalIntegerCocycle p E l m :=
    coordinateQuadratic_add_form E (p.latticeEquiv l) (p.latticeEquiv m)
  have hquadC := congrArg (fun n : ℤ => (n : ℂ)) hquad
  push_cast at hquadC
  simp only [canonicalLog, Submodule.coe_add, map_add]
  linear_combination hHerm + ((Real.pi : ℂ) * I) * hquadC

/-- Antisymmetrizing the actual integer defect gives the original positive alternating form. -/
theorem canonicalIntegerCocycle_antisymm (p : PeriodDomain) (E : Fin 6 → ℤ)
    (l m : p.lattice) :
    canonicalIntegerCocycle p E l m - canonicalIntegerCocycle p E m l =
      coordinateForm E (p.latticeEquiv l) (p.latticeEquiv m) := by
  simp [canonicalIntegerCocycle, Fin.sum_univ_succ, coefficientPair,
    coordinateForm_apply, coordinateValue]
  ring

/-- Adding the prescribed integral forms adds their literal upper-triangular cocycles. -/
theorem canonicalIntegerCocycle_add (p : PeriodDomain) (E F : Fin 6 → ℤ)
    (l m : p.lattice) :
    canonicalIntegerCocycle p (E + F) l m =
      canonicalIntegerCocycle p E l m + canonicalIntegerCocycle p F l m := by
  simp only [canonicalIntegerCocycle, Pi.add_apply, add_mul, Finset.sum_add_distrib]

/-- Integer scaling scales the explicit unwrapped cocycle, with no branch correction. -/
theorem canonicalIntegerCocycle_intMul (p : PeriodDomain) (r : ℤ) (E : Fin 6 → ℤ)
    (l m : p.lattice) :
    canonicalIntegerCocycle p (r • E) l m = r * canonicalIntegerCocycle p E l m := by
  simp only [canonicalIntegerCocycle, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

end Wikipedia.HopfProblem.PeriodTorusLineBundleChernLog
