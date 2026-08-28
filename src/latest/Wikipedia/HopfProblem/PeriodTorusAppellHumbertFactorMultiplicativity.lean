import Wikipedia.HopfProblem.PeriodTorusAppellHumbertFactor

/-!
# Addition and integer scaling of canonical factors

Adding the integral coefficient forms multiplies the actual factors.
Integer scaling gives the corresponding integer power, including negative
powers of their nonzero complex values.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusAppellHumbert

open Complex PeriodTorusTypeOneOne

theorem tangentForm_add_coefficients (p : PeriodDomain) (E F : Fin 6 → ℤ) :
    tangentForm p (E + F) = tangentForm p E + tangentForm p F := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  simp only [tangentForm_apply, LinearMap.add_apply, coordinateForm_apply, coordinateValue,
    Pi.add_apply, Int.cast_add]
  ring

theorem integralType_add (p : PeriodDomain) (E F : Fin 6 → ℤ)
    (hE : IsTypeOneOne (tangentForm p E)) (hF : IsTypeOneOne (tangentForm p F)) :
    IsTypeOneOne (tangentForm p (E + F)) := by
  rw [tangentForm_add_coefficients]
  intro x y
  simp only [LinearMap.add_apply, hE x y, hF x y]

theorem integralType_zsmul (p : PeriodDomain) (n : ℤ) (E : Fin 6 → ℤ)
    (hE : IsTypeOneOne (tangentForm p E)) : IsTypeOneOne (tangentForm p (n • E)) := by
  rw [tangentForm_zsmul]
  exact hE.smul (tangentForm p E) (n : ℝ)

theorem integralHermitian_add_coefficients (p : PeriodDomain) (E F : Fin 6 → ℤ)
    (hE : IsTypeOneOne (tangentForm p E)) (hF : IsTypeOneOne (tangentForm p F)) :
    integralHermitian p (E + F) (integralType_add p E F hE hF) =
      integralHermitian p E hE + integralHermitian p F hF := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  apply Complex.ext <;>
    simp [integralHermitian, tangentForm_add_coefficients, LinearMap.add_apply]

theorem integralHermitian_zsmul (p : PeriodDomain) (n : ℤ) (E : Fin 6 → ℤ)
    (hE : IsTypeOneOne (tangentForm p E)) :
    integralHermitian p (n • E) (integralType_zsmul p n E hE) = n • integralHermitian p E hE := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  change hermitianValue (tangentForm p (n • E)) x y = n • hermitianValue (tangentForm p E) x y
  rw [tangentForm_zsmul]
  apply Complex.ext <;> simp [hermitianValue, LinearMap.smul_apply]

theorem appellHumbertExponent_add (H K : PeriodTorusTheta.HermitianForm)
    (l z : ComplexPlane₂) :
    appellHumbertExponent (H + K) l z =
      appellHumbertExponent H l z + appellHumbertExponent K l z := by
  simp only [appellHumbertExponent, LinearMap.add_apply]
  ring

theorem appellHumbertExponent_zsmul (n : ℤ) (H : PeriodTorusTheta.HermitianForm)
    (l z : ComplexPlane₂) :
    appellHumbertExponent (n • H) l z = (n : ℂ) * appellHumbertExponent H l z := by
  simp only [appellHumbertExponent, LinearMap.smul_apply, zsmul_eq_mul]
  ring

theorem integralFactor_add_coefficients (p : PeriodDomain) (E F : Fin 6 → ℤ)
    (hE : IsTypeOneOne (tangentForm p E)) (hF : IsTypeOneOne (tangentForm p F))
    (l : p.lattice) (z : ComplexPlane₂) :
    (integralFactor p (E + F) (integralType_add p E F hE hF)).factor l z =
      (integralFactor p E hE).factor l z * (integralFactor p F hF).factor l z := by
  apply Units.ext
  change latticeSemicharacter p (E + F) l * Complex.exp
      (appellHumbertExponent (integralHermitian p (E + F) (integralType_add p E F hE hF)) l z) =
    (latticeSemicharacter p E l * Complex.exp
      (appellHumbertExponent (integralHermitian p E hE) l z)) *
    (latticeSemicharacter p F l * Complex.exp
      (appellHumbertExponent (integralHermitian p F hF) l z))
  rw [latticeSemicharacter_add_coefficients, integralHermitian_add_coefficients p E F hE hF,
    appellHumbertExponent_add, Complex.exp_add]
  ring

theorem integralFactor_zsmul (p : PeriodDomain) (n : ℤ) (E : Fin 6 → ℤ)
    (hE : IsTypeOneOne (tangentForm p E)) (l : p.lattice) (z : ComplexPlane₂) :
    (integralFactor p (n • E) (integralType_zsmul p n E hE)).factor l z =
      ((integralFactor p E hE).factor l z) ^ n := by
  apply Units.ext
  rw [Units.val_zpow_eq_zpow_val]
  change latticeSemicharacter p (n • E) l * Complex.exp
      (appellHumbertExponent (integralHermitian p (n • E) (integralType_zsmul p n E hE)) l z) =
    (latticeSemicharacter p E l * Complex.exp
      (appellHumbertExponent (integralHermitian p E hE) l z)) ^ n
  rw [latticeSemicharacter_zsmul, integralHermitian_zsmul p n E hE, appellHumbertExponent_zsmul,
    Complex.exp_int_mul, mul_zpow]

end Wikipedia.HopfProblem.PeriodTorusAppellHumbert
