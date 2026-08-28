import Wikipedia.HopfProblem.PeriodFamilyCircleOrbitLinearBasic

/-!
# The exact projected period columns and real delta kernel

The literal projection sends the four original period columns to the
three projected basis vectors and zero. Its composition with the native
period-coordinate equivalence forgets precisely the last real coordinate.
Its kernel is exactly the original real delta line, not an assumed kernel
of a separately chosen linear model.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.PeriodFamilyCircleOrbit

@[simp] theorem linearProjection_basis_zero (p : PeriodDomain) :
    linearProjection p (p.basis 0) = (6 * p.val.μ, 1) := by
  rw [PeriodDomain.basis_apply, linearProjection_apply]
  change (6 * p.val.μ,
    (p.val.β.im - (p.val.μ.im / p.val.τ.im) * (6 * p.val.μ).im) /
      p.val.discriminant) = (6 * p.val.μ, 1)
  have h : p.val.β.im - (p.val.μ.im / p.val.τ.im) * (6 * p.val.μ).im =
      p.val.discriminant := by
    simp [PeriodPoint.discriminant, Complex.mul_im]
    ring
  rw [h, div_self (discriminant_ne_zero p)]

@[simp] theorem linearProjection_basis_one (p : PeriodDomain) :
    linearProjection p (p.basis 1) = (p.val.τ, 0) := by
  rw [PeriodDomain.basis_apply, linearProjection_apply]
  change (p.val.τ,
    (p.val.μ.im - (p.val.μ.im / p.val.τ.im) * p.val.τ.im) /
      p.val.discriminant) = (p.val.τ, 0)
  rw [div_mul_cancel₀ _ (tau_im_ne_zero p), sub_self, zero_div]

@[simp] theorem linearProjection_basis_two (p : PeriodDomain) :
    linearProjection p (p.basis 2) = (1, 0) := by
  rw [PeriodDomain.basis_apply, linearProjection_apply]
  simp [PeriodPoint.matrix]

@[simp] theorem linearProjection_basis_three (p : PeriodDomain) :
    linearProjection p (p.basis 3) = 0 := by
  rw [PeriodDomain.basis_apply, linearProjection_apply]
  simp [PeriodPoint.matrix]

/-- The first three original period columns are the literal projected real basis. -/
theorem linearProjection_basis_castSucc (p : PeriodDomain) (j : Fin 3) :
    linearProjection p (p.basis j.castSucc) =
      projectedPeriods p (Pi.basisFun ℝ (Fin 3) j) := by
  fin_cases j
  · change linearProjection p (p.basis 0) = projectedPeriods p (Pi.basisFun ℝ (Fin 3) 0)
    rw [linearProjection_basis_zero]
    simp [projectedPeriods_apply, Pi.basisFun_apply]
  · change linearProjection p (p.basis 1) = projectedPeriods p (Pi.basisFun ℝ (Fin 3) 1)
    rw [linearProjection_basis_one]
    simp [projectedPeriods_apply, Pi.basisFun_apply]
  · change linearProjection p (p.basis 2) = projectedPeriods p (Pi.basisFun ℝ (Fin 3) 2)
    rw [linearProjection_basis_two]
    simp [projectedPeriods_apply, Pi.basisFun_apply]

/-- Projection of the unchanged native period map forgets exactly the real delta coordinate. -/
theorem linearProjection_periodEquiv (p : PeriodDomain) (x : Elliptic.RealCoordinates) :
    linearProjection p (Elliptic.periodEquiv p x) =
      projectedPeriods p (fun i : Fin 3 => x i.castSucc) := by
  rw [Elliptic.periodEquiv_apply, map_sum, Fin.sum_univ_four]
  simp only [map_smul, linearProjection_basis_zero, linearProjection_basis_one,
    linearProjection_basis_two, linearProjection_basis_three, smul_zero, add_zero]
  rw [projectedPeriods_apply]
  apply Prod.ext
  · change (x 0 : ℂ) * (6 * p.val.μ) + (x 1 : ℂ) * p.val.τ + (x 2 : ℂ) * 1 =
      6 * p.val.μ * (x 0 : ℂ) + p.val.τ * (x 1 : ℂ) + (x 2 : ℂ)
    ring
  · simp

/-- Every transverse invariant occurs, already in the original real period coordinates. -/
theorem linearProjection_surjective (p : PeriodDomain) :
    Function.Surjective (linearProjection p) := by
  intro y
  obtain ⟨v, rfl⟩ := (projectedPeriods p).surjective y
  refine ⟨Elliptic.periodEquiv p ![v 0, v 1, v 2, 0], ?_⟩
  rw [linearProjection_periodEquiv]
  apply congrArg (projectedPeriods p)
  ext i
  fin_cases i <;> rfl

/-- The kernel is precisely the original real vertical delta line. -/
theorem linearProjection_eq_zero_iff (p : PeriodDomain) (z : ComplexPlane₂) :
    linearProjection p z = 0 ↔ ∃ t : ℝ, z = ![0, (t : ℂ)] := by
  constructor
  · intro h
    have h₀ : z 0 = 0 := congrArg Prod.fst h
    have h₁ : (z 1).im = 0 := by
      have hs := congrArg Prod.snd h
      change ((z 1).im - (p.val.μ.im / p.val.τ.im) * (z 0).im) /
        p.val.discriminant = 0 at hs
      simpa [h₀, discriminant_ne_zero p] using hs
    refine ⟨(z 1).re, ?_⟩
    ext i
    fin_cases i
    · exact h₀
    · exact Complex.ext rfl h₁
  · rintro ⟨t, rfl⟩
    simp [linearProjection_apply]

/-- Equality of invariants is exactly a difference in the actual real delta direction. -/
theorem linearProjection_eq_iff (p : PeriodDomain) (z w : ComplexPlane₂) :
    linearProjection p z = linearProjection p w ↔
      ∃ t : ℝ, z - w = ![0, (t : ℂ)] := by
  constructor
  · intro h
    apply (linearProjection_eq_zero_iff p (z - w)).mp
    rw [map_sub, h, sub_self]
  · intro h
    have hz := (linearProjection_eq_zero_iff p (z - w)).mpr h
    simpa only [map_sub, sub_eq_zero] using hz

end Wikipedia.HopfProblem.PeriodFamilyCircleOrbit
