import Wikipedia.HopfProblem.PeriodTorusTypeOneOneExteriorBasic
import Wikipedia.HopfProblem.PeriodTorusTypeOneOneExteriorProducts
import Wikipedia.HopfProblem.PeriodTorusTypeOneOneCoordinates

/-!
# The genuine exterior square of the source form

In the exterior algebra of the integral dual lattice, `η = u ∧ w + 6 γ ∧ δ`
has square `12 γ ∧ u ∧ w ∧ δ`. The volume element is nonzero by its actual
determinant pairing with the marked lattice basis. Hence every nonzero integral
multiple of `η` also has nonzero square.

The six-coordinate formulas are identified with actual degree-two exterior
forms and with their determinant-pairing evaluations. These statements do not
assume a comparison with cohomology or an identification of the Néron--Severi
group.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusTypeOneOne

open PeriodTorusHigherHomologyExterior

/-- The six-coordinate exterior-power element has the displayed algebra expression. -/
theorem integralExteriorForm_coe (E : Fin 6 → ℤ) :
    (integralExteriorForm E : IntegralExterior) =
      sixCoefficientExterior E latticeCovector := by
  rw [integralExteriorForm_apply]
  simp only [Submodule.coe_add, Submodule.coe_smul, exteriorPair_coe,
    sixCoefficientExterior]

theorem volumeProduct_latticeCovector :
    volumeProduct (R := ℤ) latticeCovector = volumeExterior :=
  volumeExterior_eq.symm

/-- The actual six-coordinate square, with the source's ordered volume convention. -/
theorem integralExteriorForm_sq (E : Fin 6 → ℤ) :
    (integralExteriorForm E : IntegralExterior) ^ 2 =
      (2 * (E 0 * E 5 - E 1 * E 4 + E 2 * E 3)) • volumeExterior := by
  rw [pow_two, integralExteriorForm_coe, sixCoefficientExterior_sq,
    volumeProduct_latticeCovector]

theorem integralExteriorForm_sq_eq_zero_iff (E : Fin 6 → ℤ) :
    (integralExteriorForm E : IntegralExterior) ^ 2 = 0 ↔
      E 0 * E 5 - E 1 * E 4 + E 2 * E 3 = 0 := by
  rw [integralExteriorForm_sq, smul_volumeExterior_eq_zero_iff]
  simp

/-- Evaluation of a genuine marked exterior pair is the corresponding determinant. -/
theorem exteriorPair_pairing (i j : Fin 4) (x y : Lattice) :
    dualPairingEquiv 2 (exteriorPair i j) (exteriorPower.ιMulti ℤ 2 ![x, y]) =
      x i * y j - x j * y i := by
  rw [exteriorPair, dualPairingEquiv_ιMulti_ιMulti]
  simp [Matrix.det_fin_two]

/-- The six-coordinate alternating form is the actual exterior-dual pairing. -/
theorem integralExteriorForm_pairing (E : Fin 6 → ℤ) (x y : Lattice) :
    dualPairingEquiv 2 (integralExteriorForm E) (exteriorPower.ιMulti ℤ 2 ![x, y]) =
      coordinateForm E x y := by
  rw [integralExteriorForm_apply]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    exteriorPair_pairing, smul_eq_mul, coordinateForm_apply, coordinateValue]

theorem etaExterior_eq_sixCoefficientExterior :
    etaExterior = sixCoefficientExterior ![0, 0, 6, 1, 0, 0] latticeCovector := by
  rw [← integralExteriorForm_coe, integralExteriorForm_eta]
  rfl

/-- The square of the source form in the actual integral exterior algebra. -/
theorem etaExterior_mul_self :
    etaExterior * etaExterior = (12 : ℤ) • volumeExterior := by
  rw [etaExterior_eq_sixCoefficientExterior, sixCoefficientExterior_sq,
    volumeProduct_latticeCovector]
  congr 1

theorem etaExterior_sq : etaExterior ^ 2 = (12 : ℤ) • volumeExterior := by
  rw [pow_two, etaExterior_mul_self]

/-- An integer multiple has square `12 n²` times the genuine volume element. -/
theorem zsmul_etaExterior_sq (n : ℤ) :
    (n • etaExterior) ^ 2 = (12 * n ^ 2) • volumeExterior := by
  rw [pow_two, smul_mul_assoc, mul_smul_comm, etaExterior_mul_self, smul_smul, smul_smul]
  congr 1
  ring

theorem zsmul_etaExterior_sq_eq_zero_iff (n : ℤ) :
    (n • etaExterior) ^ 2 = 0 ↔ n = 0 := by
  rw [zsmul_etaExterior_sq, smul_volumeExterior_eq_zero_iff]
  simp

theorem zsmul_etaExterior_sq_ne_zero (n : ℤ) (hn : n ≠ 0) :
    (n • etaExterior) ^ 2 ≠ 0 :=
  (zsmul_etaExterior_sq_eq_zero_iff n).not.mpr hn

theorem etaExterior_sq_ne_zero : etaExterior ^ 2 ≠ 0 := by
  simpa using zsmul_etaExterior_sq_ne_zero 1 (by decide)

theorem etaExterior_ne_zero : etaExterior ≠ 0 := by
  intro h
  exact etaExterior_sq_ne_zero (by simp [h])

theorem etaExteriorPower_ne_zero : etaExteriorPower ≠ 0 := by
  intro h
  exact etaExterior_ne_zero (congrArg Subtype.val h)

end Wikipedia.HopfProblem.PeriodTorusTypeOneOne
