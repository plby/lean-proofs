import Wikipedia.HopfProblem.EllipticEquivariantData

/-!
# Monodromy of arbitrary equivariant elliptic periods

The covariance condition on an actual holomorphic period family gives the
period-matrix identity and its real-coordinate intertwining formulas.
Nothing here identifies the family with a particular explicit example.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.Elliptic.Equivariant.Data

open SpecialPeriods

variable {j : Kind} (D : Equivariant.Data j)

/-- The family's real period isomorphism has the prescribed complex columns. -/
theorem periodEquiv_matrix (z : Disc) (x : RealCoordinates) :
    D.periods.periodEquiv z x =
      (D.periods.point z).val.matrix *ᵥ (fun i => (x i : ℂ)) := by
  rw [HolomorphicPeriodMap.periodEquiv_coordinates]
  ext i
  fin_cases i <;>
    simp [PeriodPoint.matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

/-- Family period coordinates agree with the basis-based coordinates on
each actual complex period torus. -/
theorem periodEquiv_eq_periodEquiv (z : Disc) (x : RealCoordinates) :
    D.periods.periodEquiv z x = Elliptic.periodEquiv (D.periods.point z) x := by
  rw [D.periodEquiv_matrix, Elliptic.periodEquiv_matrix]

theorem periodEquiv_linearEquiv_eq (z : Disc) :
    D.periods.periodEquiv z = (Elliptic.periodEquiv (D.periods.point z)).toLinearEquiv := by
  apply LinearEquiv.ext
  intro x
  exact D.periodEquiv_eq_periodEquiv z x

theorem periodEquiv_symm_eq_periodEquiv_symm (z : Disc) (w : ComplexPlane₂) :
    (D.periods.periodEquiv z).symm w =
      (Elliptic.periodEquiv (D.periods.point z)).symm w := by
  rw [D.periodEquiv_linearEquiv_eq]
  rfl

/-- The full covariance identity `Π(gz) A = R(z) Π(z)` follows from the
period transformation law and the checked contragredient matrices. -/
theorem matrix_covariance (z : Disc) :
    (D.periods.point (familyRotation j z)).val.matrix *
        j.matrix.map (Int.castRingHom ℂ) =
      linearMatrix j (D.periods.point z) * (D.periods.point z).val.matrix := by
  rw [D.covariance z]
  cases j
  · change (D.periods.point z).val.step₁.matrix * A₁.map (Int.castRingHom ℂ) =
      (D.periods.point z).val.R₁ * (D.periods.point z).val.matrix
    rw [PeriodPoint.step₁_matrix _ ((D.periods.point z).val.τ_ne_zero
      (D.periods.point z).property.1), Matrix.mul_assoc]
    have h : (T₁.map (Int.castRingHom ℂ)).transpose * A₁.map (Int.castRingHom ℂ) = 1 := by
      change T₁.transpose.map (Int.castRingHom ℂ) * A₁.map (Int.castRingHom ℂ) = 1
      rw [← Matrix.map_mul, show T₁.transpose * A₁ = 1 by decide]
      simp
    rw [h, Matrix.mul_one]
  · change (D.periods.point z).val.step₂.matrix * A₂.map (Int.castRingHom ℂ) =
      (D.periods.point z).val.R₂ * (D.periods.point z).val.matrix
    rw [PeriodPoint.step₂_matrix _ ((D.periods.point z).val.τ_ne_zero
      (D.periods.point z).property.1), Matrix.mul_assoc]
    have h : (T₂.map (Int.castRingHom ℂ)).transpose * A₂.map (Int.castRingHom ℂ) = 1 := by
      change T₂.transpose.map (Int.castRingHom ℂ) * A₂.map (Int.castRingHom ℂ) = 1
      rw [← Matrix.map_mul, show T₂.transpose * A₂ = 1 by decide]
      simp
    rw [h, Matrix.mul_one]

/-- Varying complex period coordinates intertwine the constant integral
linear action with the complex monodromy matrix. -/
theorem periodEquiv_flatLinear (z : Disc) (x : RealCoordinates) :
    D.periods.periodEquiv (familyRotation j z) (flatLinear j x) =
      linearMatrix j (D.periods.point z) *ᵥ D.periods.periodEquiv z x := by
  rw [D.periodEquiv_matrix, flatLinear_complexCast, Matrix.mulVec_mulVec,
    D.periodEquiv_matrix, Matrix.mulVec_mulVec, D.matrix_covariance]

/-- The same intertwining identity in inverse period coordinates. -/
theorem periodEquiv_symm_linearMatrix (z : Disc) (w : ComplexPlane₂) :
    (D.periods.periodEquiv (familyRotation j z)).symm
        (linearMatrix j (D.periods.point z) *ᵥ w) =
      flatLinear j ((D.periods.periodEquiv z).symm w) := by
  apply (D.periods.periodEquiv (familyRotation j z)).injective
  rw [LinearEquiv.apply_symm_apply, D.periodEquiv_flatLinear,
    LinearEquiv.apply_symm_apply]

end Wikipedia.HopfProblem.Elliptic.Equivariant.Data
