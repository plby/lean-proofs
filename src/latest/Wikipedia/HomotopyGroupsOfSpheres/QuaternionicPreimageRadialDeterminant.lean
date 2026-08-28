import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSeedRadialDeterminant
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicMidpointFourInputs

/-! # The radial determinant is positive at every explicit preimage

Unit complex scaling rotates the two square-sum rows with determinant one.
The sign actions preserve all squared coordinates and coordinate norms.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary

open QuaternionicBottMatrix

def radialScaleMatrix (q : ℂ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![Complex.normSq q, 0, 0;
     0, (q ^ 2).re, -(q ^ 2).im;
     0, (q ^ 2).im, (q ^ 2).re]

theorem radialMatrix_smul (q : ℂ) (z : Vector) :
    radialMatrix (q • z) = radialScaleMatrix q * radialMatrix z := by
  ext r s
  fin_cases r <;>
    simp [radialMatrix, radialScaleMatrix, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.cons_val_two, map_mul, mul_pow, Complex.mul_re, Complex.mul_im] <;> ring

theorem radialScaleMatrix_det (q : ℂ) :
    (radialScaleMatrix q).det = Complex.normSq q ^ 3 := by
  calc
    _ = Complex.normSq q * Complex.normSq (q ^ 2) := by
      simp [radialScaleMatrix, Matrix.det_fin_three, Complex.normSq_apply]
      ring
    _ = _ := by rw [map_pow]; ring

theorem radialMatrix_smul_det (q : ℂ) (z : Vector) :
    (radialMatrix (q • z)).det = Complex.normSq q ^ 3 * (radialMatrix z).det := by
  rw [radialMatrix_smul, Matrix.det_mul, radialScaleMatrix_det]

theorem unitary_normSq (q : unitary ℂ) : Complex.normSq q.val = 1 := by
  rw [Complex.normSq_eq_norm_sq, unitary_complex_norm, one_pow]

theorem signs_normSq (x y : Bool) (r : Fin 3) : Complex.normSq (signs x y r) = 1 := by
  have he : (Complex.normSq (signs x y r) : ℂ) = 1 := by
    rw [Complex.normSq_eq_conj_mul_self]
    change star (signs x y r) * signs x y r = 1
    rw [signs_star, ← pow_two, signs_sq]
  exact_mod_cast he

theorem radialMatrix_signVector (x y : Bool) (z : Vector) :
    radialMatrix (signVector x y z) = radialMatrix z := by
  ext r s
  fin_cases r <;>
    simp [radialMatrix, signVector, map_mul, signs_normSq, mul_pow, signs_sq,
      Matrix.cons_val_two]

theorem radialMatrix_rotated_phaseInput_det_pos (u : unitary ℂ) (b : Bool × Bool) :
    0 < (radialMatrix (rotationSphere (phaseInput u b)).val).det := by
  rw [phaseInput, rotationSphere_involutive]
  change 0 < (radialMatrix ((negativePhase u).val •
    signVector b.1 b.2 MidpointSeed.vector)).det
  rw [radialMatrix_smul_det, unitary_normSq, one_pow, one_mul, radialMatrix_signVector]
  exact MidpointSeed.radialMatrix_vector_det_pos

theorem rotated_phaseInput_coordinate_ne_zero (u : unitary ℂ) (b : Bool × Bool) (r : Fin 3) :
    (rotationSphere (phaseInput u b)).val r ≠ 0 := by
  rw [phaseInput, rotationSphere_involutive]
  change (negativePhase u).val * (signs b.1 b.2 r * MidpointSeed.rotatedInput.val r) ≠ 0
  have hs : signs b.1 b.2 r ≠ 0 := by
    intro h
    have he := signs_sq b.1 b.2 r
    rw [h, zero_pow (by decide : 2 ≠ 0)] at he
    exact zero_ne_one he
  exact mul_ne_zero (unitary_complex_ne_zero _) (mul_ne_zero hs
    (MidpointSeed.rotatedInput_coordinate_ne_zero r))

theorem rotated_phaseInput_squareSum_normSq_lt_one (u : unitary ℂ)
    (hu : u.val ^ 3 = -1) (b : Bool × Bool) :
    Complex.normSq (squareSum (rotationSphere (phaseInput u b)).val) < 1 := by
  rw [midpoint_rotated_squareSum (phaseInput u b) u hu (phaseInput_matrix u hu b),
    map_mul, Complex.normSq_neg, Complex.star_def, Complex.normSq_conj,
    unitary_normSq, one_mul]
  exact traceRoot_normSq_lt_one

theorem sphere_curve_rotated_phaseInput_kernel (z : ℝ → UnitSphere) (v : Vector) (x : ℝ)
    (hz : ∀ r, HasDerivAt (fun t ↦ (z t).val r) (v r) x)
    (hv : symmetricVariation (z x).val v = 0)
    (u : unitary ℂ) (hu : u.val ^ 3 = -1) (b : Bool × Bool)
    (hx : z x = rotationSphere (phaseInput u b)) : v = 0 := by
  apply sphere_curve_diagonal_kernel z v x hz hv (fun r ↦ u.val * targetEigenvalues r)
  · rw [hx]
    exact midpoint_diagonalized _ _ (phaseInput_matrix u hu b)
  · intro r
    rw [hx]
    exact rotated_phaseInput_coordinate_ne_zero u b r
  · rw [hx]
    exact rotated_phaseInput_squareSum_normSq_lt_one u hu b
  · rw [hx]
    exact ne_of_gt (radialMatrix_rotated_phaseInput_det_pos u b)

end Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary
