import Wikipedia.HopfProblem.PeriodTorusAppellHumbertFactorBasic
import Wikipedia.HopfProblem.PeriodTorusAppellHumbertSemicharacter

/-!
# Canonical Appell--Humbert factors for integral forms of type `(1,1)`

The semicharacter, Hermitian form, and factor are all constructed on the
actual marked period lattice. The transformation law is exactly the law
already used for theta functions, rather than an assumed section comparison.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusAppellHumbert

open Complex PeriodTorusTypeOneOne
open scoped ContDiff

/-- The canonical holomorphic factor for an integral tangent form of type `(1,1)`. -/
def integralFactor (p : PeriodDomain) (E : Fin 6 → ℤ)
    (hType : IsTypeOneOne (tangentForm p E)) : FactorOfAutomorphy p :=
  hermitianFactor p (integralHermitian p E hType) (integralHermitian_isHermitian p E hType)
    (latticeSemicharacter p E) (latticeSemicharacter_zero p E)
    (latticeSemicharacter_ne_zero p E) (by
      intro l m
      simpa only [integralHermitian_lattice_im, Complex.ofReal_intCast] using
        latticeSemicharacter_add_neg p E l m)

/-- The factor is the displayed Appell--Humbert expression as an actual nonzero complex number. -/
@[simp]
theorem integralFactor_coe (p : PeriodDomain) (E : Fin 6 → ℤ)
    (hType : IsTypeOneOne (tangentForm p E)) (l : p.lattice) (z : ComplexPlane₂) :
    ((integralFactor p E hType).factor l z : ℂ) =
      latticeSemicharacter p E l * Complex.exp
        ((Real.pi : ℂ) * integralHermitian p E hType z l +
          ((Real.pi : ℂ) / 2) * integralHermitian p E hType l l) := rfl

theorem integralFactor_holomorphic (p : PeriodDomain) (E : Fin 6 → ℤ)
    (hType : IsTypeOneOne (tangentForm p E)) (l : p.lattice) :
    ContDiff ℂ ω (fun z => ((integralFactor p E hType).factor l z : ℂ)) :=
  (integralFactor p E hType).holomorphic_factor l

theorem integralFactor_norm (p : PeriodDomain) (E : Fin 6 → ℤ)
    (hType : IsTypeOneOne (tangentForm p E)) (l : p.lattice) (z : ComplexPlane₂) :
    ‖((integralFactor p E hType).factor l z : ℂ)‖ =
      Real.exp (Real.pi * (integralHermitian p E hType z l).re +
        (Real.pi / 2) * (integralHermitian p E hType l l).re) := by
  rw [integralFactor_coe, norm_mul, latticeSemicharacter_norm, one_mul, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re]

/-- The concrete factor transformation law is exactly the theta-function automorphy law. -/
theorem integralFactor_automorphy_iff (p : PeriodDomain) (E : Fin 6 → ℤ)
    (hType : IsTypeOneOne (tangentForm p E)) (θ : ComplexPlane₂ → ℂ) :
    (∀ (l : p.lattice) z,
      θ (z + l) = ((integralFactor p E hType).factor l z : ℂ) * θ z) ↔
      PeriodTorusTheta.AppellHumbertAutomorphy p (integralHermitian p E hType)
        (latticeSemicharacter p E) θ := by
  simp only [integralFactor_coe, PeriodTorusTheta.AppellHumbertAutomorphy]

end Wikipedia.HopfProblem.PeriodTorusAppellHumbert
