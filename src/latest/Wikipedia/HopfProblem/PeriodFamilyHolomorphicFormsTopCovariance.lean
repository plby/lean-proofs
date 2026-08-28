import Wikipedia.HopfProblem.PeriodFamilyHolomorphicFormsCovariance

/-!
# The determinant calculation for top-form covariance

The function evaluated below is the literal three-dimensional coordinate
determinant, not a replacement type of differential form. The actual
block Jacobian of a period-family transformation multiplies it by the
base derivative times the determinant of the fibre matrix. Evaluation
of a full top-covector pullback identity gives equation (9.10).
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicForms

/-- The determinant of the three coordinate column vectors. -/
def coordinateVolume (u v w : ℂ × ComplexPlane₂) : ℂ :=
  u.1 * (v.2 0 * w.2 1 - v.2 1 * w.2 0) -
    v.1 * (u.2 0 * w.2 1 - u.2 1 * w.2 0) +
    w.1 * (u.2 0 * v.2 1 - u.2 1 * v.2 0)

theorem coordinateVolume_eq_det (u v w : ℂ × ComplexPlane₂) :
    coordinateVolume u v w = Matrix.det
      !![u.1, v.1, w.1; u.2 0, v.2 0, w.2 0; u.2 1, v.2 1, w.2 1] := by
  rw [Matrix.det_fin_three]
  change coordinateVolume u v w =
    u.1 * v.2 0 * w.2 1 - u.1 * w.2 0 * v.2 1 -
      v.1 * u.2 0 * w.2 1 + v.1 * w.2 0 * u.2 1 +
      w.1 * u.2 0 * v.2 1 - w.1 * v.2 0 * u.2 1
  dsimp only [coordinateVolume]
  ring

/-- The literal block Jacobian, with an arbitrary fibre-valued shear column. -/
def blockJacobian (a : ℂ) (R : Matrix (Fin 2) (Fin 2) ℂ) (s : ComplexPlane₂)
    (u : ℂ × ComplexPlane₂) : ℂ × ComplexPlane₂ :=
  (a * u.1, R *ᵥ u.2 + u.1 • s)

/-- The shear column does not change the determinant of the block Jacobian. -/
theorem coordinateVolume_blockJacobian (a : ℂ) (R : Matrix (Fin 2) (Fin 2) ℂ)
    (s : ComplexPlane₂) (u v w : ℂ × ComplexPlane₂) :
    coordinateVolume (blockJacobian a R s u) (blockJacobian a R s v)
        (blockJacobian a R s w) = a * R.det * coordinateVolume u v w := by
  simp only [coordinateVolume, blockJacobian, Matrix.det_fin_two,
    Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

@[simp] theorem coordinateVolume_basis :
    coordinateVolume (1, 0) (0, Pi.single (0 : Fin 2) 1)
      (0, Pi.single (1 : Fin 2) 1) = 1 := by
  simp [coordinateVolume]

/-- An actual period shear has determinant one. -/
theorem coordinateVolume_periodShear (s : ComplexPlane₂) (u v w : ℂ × ComplexPlane₂) :
    coordinateVolume (blockJacobian 1 1 s u) (blockJacobian 1 1 s v)
      (blockJacobian 1 1 s w) = coordinateVolume u v w := by
  rw [coordinateVolume_blockJacobian]
  simp only [Matrix.det_one, mul_one, one_mul]

/-- The full top-covector pullback equation implies its coefficient covariance. -/
theorem threeForm_covariance {B : Type*} (C : B → ℂ) (g : B → B) (dg : B → ℂ)
    (R Rdot : B → Matrix (Fin 2) (Fin 2) ℂ)
    (hpullback : ∀ z ζ u v w,
      C (g z) * coordinateVolume
        (blockJacobian (dg z) (R z) (Rdot z *ᵥ ζ) u)
        (blockJacobian (dg z) (R z) (Rdot z *ᵥ ζ) v)
        (blockJacobian (dg z) (R z) (Rdot z *ᵥ ζ) w) =
      C z * coordinateVolume u v w)
    (z : B) : C (g z) * dg z * (R z).det = C z := by
  have h := hpullback z 0 (1, 0) (0, Pi.single (0 : Fin 2) 1)
    (0, Pi.single (1 : Fin 2) 1)
  simpa only [coordinateVolume_blockJacobian, coordinateVolume_basis, mul_one, mul_assoc]
    using h

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicForms
