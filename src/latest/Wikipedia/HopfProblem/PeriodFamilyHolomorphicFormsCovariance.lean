import Wikipedia.HopfProblem.PeriodTori

/-!
# Scalar covariance identities for period-family forms

The hypotheses below are full scalar pullback evaluations under the block
Jacobian `(t, v) ↦ (dg * t, R *ᵥ v + t • (Rdot *ᵥ ζ))`. Evaluation at zero
and at the coordinate basis vectors proves the coefficient identities in
(9.8) and (9.9). No new type of differential form, or coefficient covariance
assumption, is introduced.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicForms

variable {B : Type*}

section OneForm

variable (A : B → ℂ) (C : B → ComplexPlane₂) (g : B → B) (dg : B → ℂ)
  (R Rdot : B → Matrix (Fin 2) (Fin 2) ℂ)
  (hpullback : ∀ z ζ v t,
    A (g z) * (dg z * t) +
        dotProduct (C (g z)) (R z *ᵥ v + t • (Rdot z *ᵥ ζ)) =
      A z * t + dotProduct (C z) v)

include hpullback

/-- The vertical basis vectors give the row-covector covariance in (9.8). -/
theorem oneForm_fibre_covariance (z : B) : C (g z) ᵥ* R z = C z := by
  funext i
  have h := hpullback z 0 (Pi.single i 1) 0
  simpa only [mul_zero, zero_smul, add_zero, zero_add, Matrix.dotProduct_mulVec,
    dotProduct_single_one] using h

/-- The horizontal vector at zero fibre position gives the scalar covariance in (9.8). -/
theorem oneForm_base_covariance (z : B) : A (g z) * dg z = A z := by
  simpa only [Matrix.mulVec_zero, smul_zero, add_zero, dotProduct_zero, mul_one]
    using hpullback z 0 0 1

/-- Varying the fibre position of the horizontal vector kills the derivative row in (9.8). -/
theorem oneForm_derivative_covariance (z : B) : C (g z) ᵥ* Rdot z = 0 := by
  funext i
  have h := hpullback z (Pi.single i 1) 0 1
  simp only [Matrix.mulVec_zero, zero_add, one_smul, dotProduct_zero, mul_one,
    add_zero, Matrix.dotProduct_mulVec, dotProduct_single_one] at h
  rw [oneForm_base_covariance A C g dg R Rdot hpullback z] at h
  exact add_left_cancel (h.trans ((add_zero (A z)).symm))

/-- All three one-form identities follow together from the full scalar pullback equation. -/
theorem oneForm_covariance (z : B) :
    C (g z) ᵥ* R z = C z ∧ A (g z) * dg z = A z ∧ C (g z) ᵥ* Rdot z = 0 :=
  ⟨oneForm_fibre_covariance A C g dg R Rdot hpullback z,
    oneForm_base_covariance A C g dg R Rdot hpullback z,
    oneForm_derivative_covariance A C g dg R Rdot hpullback z⟩

end OneForm

/-- The horizontal-vertical basis evaluation of a full alternating two-form gives (9.9).
The vertical-area coefficient is arbitrary: its contribution vanishes at this evaluation. -/
theorem twoForm_covariance (a : B → ℂ) (b : B → ComplexPlane₂)
    (g : B → B) (dg : B → ℂ) (R Rdot : B → Matrix (Fin 2) (Fin 2) ℂ)
    (hpullback : ∀ z ζ v w t s,
      let v' := R z *ᵥ v + t • (Rdot z *ᵥ ζ)
      let w' := R z *ᵥ w + s • (Rdot z *ᵥ ζ)
      a (g z) * (v' 0 * w' 1 - v' 1 * w' 0) +
          (dg z * t) * dotProduct (b (g z)) w' -
          (dg z * s) * dotProduct (b (g z)) v' =
        a z * (v 0 * w 1 - v 1 * w 0) +
          t * dotProduct (b z) w - s * dotProduct (b z) v)
    (z : B) : dg z • (b (g z) ᵥ* R z) = b z := by
  funext i
  have h := hpullback z 0 0 (Pi.single i 1) 1 0
  dsimp only at h
  simpa only [Matrix.mulVec_zero, smul_zero, add_zero, zero_add, Pi.zero_apply,
    mul_zero, zero_mul, mul_one, one_mul, sub_zero, dotProduct_zero,
    Matrix.dotProduct_mulVec, dotProduct_single_one, Pi.smul_apply, smul_eq_mul] using h

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicForms
