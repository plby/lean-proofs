import Wikipedia.HopfProblem.EllipticFixedPeriods
import Wikipedia.HopfProblem.EllipticPeriodCoordinates

/-!
# Linear monodromy on the fixed elliptic period tori

At a fixed period the complex monodromy matrices preserve the actual
period lattice.  Their induced biholomorphisms are conjugate, in real
period coordinates, to the specified integral order-three and order-four
matrices.
-/

noncomputable section

open scoped Matrix ContDiff

namespace Wikipedia.HopfProblem.Elliptic

/-- The complex linear matrix associated with the elliptic generator. -/
def linearMatrix (j : Kind) (p : PeriodDomain) : Matrix (Fin 2) (Fin 2) ℂ :=
  match j with
  | .three => p.val.R₁
  | .four => p.val.R₂

/-- The linear monodromy equivalence on the complex covering space. -/
def linearEquiv (j : Kind) (p : FixedPeriod j) : ComplexPlane₂ ≃L[ℂ] ComplexPlane₂ :=
  match j with
  | .three => p.val.R₁Equiv
  | .four => p.val.R₂Equiv

theorem linearEquiv_apply (j : Kind) (p : FixedPeriod j) (z : ComplexPlane₂) :
    linearEquiv j p z = linearMatrix j p.val *ᵥ z := by
  cases j
  · exact p.val.R₁Equiv_apply z
  · exact p.val.R₂Equiv_apply z

/-- Fixedness of the period makes the lattice covariance an invariance. -/
theorem linearEquiv_map_lattice (j : Kind) (p : FixedPeriod j) :
    p.val.lattice.map ((linearEquiv j p).toLinearEquiv.restrictScalars ℤ).toLinearMap =
      p.val.lattice := by
  cases j
  · exact p.val.R₁Equiv_map_lattice.trans (congrArg PeriodDomain.lattice p.property)
  · exact p.val.R₂Equiv_map_lattice.trans (congrArg PeriodDomain.lattice p.property)

/-- The complex and integral linear monodromies have the same period columns. -/
theorem linearMatrix_period_matrix (j : Kind) (p : FixedPeriod j) :
    linearMatrix j p.val * p.val.val.matrix =
      p.val.val.matrix * j.matrix.map (Int.castRingHom ℂ) := by
  cases j
  · have hp : p.val.val.step₁ = p.val.val := congrArg Subtype.val p.property
    have hm := p.val.val.step₁_matrix (p.val.val.τ_ne_zero p.val.property.1)
    rw [hp] at hm
    have hTA : (T₁.map (Int.castRingHom ℂ)).transpose * A₁.map (Int.castRingHom ℂ) = 1 := by
      have h : T₁.transpose * A₁ = 1 := by decide
      simpa only [Matrix.map_mul, Matrix.transpose_map, Matrix.map_one, map_zero, map_one] using
        congrArg (fun A : LatticeMatrix => A.map (Int.castRingHom ℂ)) h
    simpa only [linearMatrix, Kind.matrix, Matrix.mul_assoc, hTA, Matrix.mul_one] using
      (congrArg (fun A => A * A₁.map (Int.castRingHom ℂ)) hm).symm
  · have hp : p.val.val.step₂ = p.val.val := congrArg Subtype.val p.property
    have hm := p.val.val.step₂_matrix (p.val.val.τ_ne_zero p.val.property.1)
    rw [hp] at hm
    have hTA : (T₂.map (Int.castRingHom ℂ)).transpose * A₂.map (Int.castRingHom ℂ) = 1 := by
      have h : T₂.transpose * A₂ = 1 := by decide
      simpa only [Matrix.map_mul, Matrix.transpose_map, Matrix.map_one, map_zero, map_one] using
        congrArg (fun A : LatticeMatrix => A.map (Int.castRingHom ℂ)) h
    simpa only [linearMatrix, Kind.matrix, Matrix.mul_assoc, hTA, Matrix.mul_one] using
      (congrArg (fun A => A * A₂.map (Int.castRingHom ℂ)) hm).symm

/-- Real and complex scalar extension give the same integral linear action. -/
theorem flatLinear_complexCast (j : Kind) (x : RealCoordinates) :
    (fun i => ((flatLinear j x) i : ℂ)) =
      (j.matrix.map (Int.castRingHom ℂ)) *ᵥ (fun i => (x i : ℂ)) := by
  ext i
  simp [flatLinear, Matrix.mulVec, dotProduct]

/-- Period coordinates intertwine the complex and integral monodromies. -/
theorem linearEquiv_periodEquiv (j : Kind) (p : FixedPeriod j) (x : RealCoordinates) :
    linearEquiv j p (periodEquiv p.val x) = periodEquiv p.val (flatLinear j x) := by
  rw [linearEquiv_apply, periodEquiv_matrix, periodEquiv_matrix, flatLinear_complexCast,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, linearMatrix_period_matrix]

/-- Linear monodromy descends to a genuine biholomorphism of the fixed torus. -/
def linearBiholomorph (j : Kind) (p : FixedPeriod j) :
    Diffeomorph (modelWithCornersSelf ℂ ComplexPlane₂)
      (modelWithCornersSelf ℂ ComplexPlane₂) p.val.Torus p.val.Torus ω :=
  DiscreteQuotient.linearBiholomorph p.val.lattice p.val.lattice
    (linearEquiv j p) (linearEquiv_map_lattice j p)

@[simp] theorem linearBiholomorph_mkQ (j : Kind) (p : FixedPeriod j) (z : ComplexPlane₂) :
    linearBiholomorph j p (p.val.lattice.mkQ z) =
      p.val.lattice.mkQ (linearEquiv j p z) := rfl

/-- The induced torus biholomorphism acts by the integral matrix in flat coordinates. -/
theorem linearBiholomorph_flatProjection (j : Kind) (p : FixedPeriod j)
    (x : RealCoordinates) :
    linearBiholomorph j p (flatProjection p.val x) = flatProjection p.val (flatLinear j x) := by
  change linearBiholomorph j p (p.val.lattice.mkQ (periodEquiv p.val x)) = _
  rw [linearBiholomorph_mkQ, linearEquiv_periodEquiv]
  rfl

end Wikipedia.HopfProblem.Elliptic
