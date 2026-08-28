import Wikipedia.HomotopyGroupsOfSpheres.ComplexTraceDifferential

/-! # Kernel constraints for actual curves on the unit five-sphere

A zero symmetric-image derivative forces the original matrix derivative
to satisfy the same conjugation relation as the matrix. At a diagonal
image, each nonzero sphere coordinate can then move only along its real
radial line. The sphere and trace tangency constraints remain available.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary

open QuaternionicSymmetricMatrices

theorem sphere_curve_norm_tangent (z : ℝ → UnitSphere) (v : Vector) (x : ℝ)
    (hz : ∀ r, HasDerivAt (fun t ↦ (z t).val r) (v r) x) :
    ∑ r, (star (v r) * (z x).val r + star ((z x).val r) * v r) = 0 := by
  have he := HasDerivAt.fun_sum (u := Finset.univ)
    (fun r (_ : r ∈ Finset.univ) ↦ (hz r).star.mul (hz r))
  have hf : (fun t : ℝ ↦ ∑ r, ((fun t ↦ star ((z t).val r)) *
      (fun t ↦ (z t).val r)) t) = fun _ ↦ (1 : ℂ) := by
    funext t
    exact normPolynomial_unit (z t)
  rw [hf] at he
  exact he.unique (hasDerivAt_const x 1)

theorem hasDerivAt_symmetricMap_entry (z : ℝ → UnitSphere) (v : Vector) (x : ℝ)
    (hz : ∀ r, HasDerivAt (fun t ↦ (z t).val r) (v r) x) (r s : Fin 3) :
    HasDerivAt (fun t ↦ (symmetricMap (z t)).val.val r s)
      (symmetricVariation (z x).val v r s) x := by
  convert hasDerivAt_symmetricMatrix_entry (fun t r ↦ (z t).val r) v x hz r s using 1
  try rfl
  funext t
  exact congrArg (fun A : Matrix (Fin 3) (Fin 3) ℂ ↦ A r s) (symmetricMap_val (z t))

theorem sphere_curve_matrixVariation_conjugate (z : ℝ → UnitSphere) (v : Vector) (x : ℝ)
    (hz : ∀ r, HasDerivAt (fun t ↦ (z t).val r) (v r) x)
    (hv : symmetricVariation (z x).val v = 0) :
    matrixVariation (z x).val v =
      (symmetricMap (z x)).val.val * conjugate (matrixVariation (z x).val v) := by
  have hB (r s : Fin 3) :
      HasDerivAt (fun t ↦ (symmetricMap (z t)).val.val r s) 0 x := by
    simpa only [hv, Matrix.zero_apply] using hasDerivAt_symmetricMap_entry z v x hz r s
  have hM := hasDerivAt_matrix_entry (fun t r ↦ (z t).val r) v x hz
  apply Matrix.ext
  intro r s
  have he := HasDerivAt.fun_sum (u := Finset.univ)
    (fun k (_ : k ∈ Finset.univ) ↦ (hB r k).mul (hM k s).star)
  have hf : (fun t : ℝ ↦ ∑ k, ((fun t ↦ (symmetricMap (z t)).val.val r k) *
      (fun t ↦ star (matrix (z t).val k s))) t) =
      fun t ↦ matrix (z t).val r s := by
    funext t
    exact (congrArg (fun A : Matrix (Fin 3) (Fin 3) ℂ ↦ A r s)
      (matrix_eq_symmetric_mul_conjugate (z t))).symm
  rw [hf] at he
  have hd := (hM r s).unique he
  simpa [Matrix.mul_apply, conjugate] using hd

theorem matrixVariation_diagonal (z v : Vector) (r : Fin 3) :
    matrixVariation z v r r = 2 * z r * v r := by
  fin_cases r <;> simp [matrixVariation, outer, crossMatrix, Matrix.cons_val_two] <;> ring

theorem phase_velocity_real_mul (z v d : ℂ) (hz : z ≠ 0)
    (hb : z ^ 2 = d * star z ^ 2)
    (hv : 2 * z * v = d * (2 * star z * star v)) :
    ∃ a : ℝ, v = (a : ℂ) * z := by
  have he : v * star z = z * star v := by
    apply mul_left_cancel₀ hz
    linear_combination star z * hv / 2 - star v * hb
  have hr : star (v / z) = v / z := by
    have hd : star (v / z) = star v / star z := star_div₀ v z
    rw [hd]
    apply (div_eq_div_iff (star_ne_zero.mpr hz) hz).mpr
    linear_combination -he
  have hi : (v / z).im = 0 := by
    have h := congrArg Complex.im hr
    simp only [Complex.star_def, Complex.conj_im] at h
    linarith
  have heq : (((v / z).re : ℝ) : ℂ) = v / z := by
    apply Complex.ext
    · rfl
    · exact hi.symm
  refine ⟨(v / z).re, ?_⟩
  rw [heq, div_mul_cancel₀ _ hz]

theorem sphere_curve_diagonal_velocity_real (z : ℝ → UnitSphere) (v : Vector) (x : ℝ)
    (hz : ∀ r, HasDerivAt (fun t ↦ (z t).val r) (v r) x)
    (hv : symmetricVariation (z x).val v = 0) (d : Fin 3 → ℂ)
    (hd : (symmetricMap (z x)).val.val = Matrix.diagonal d) (r : Fin 3)
    (hr : (z x).val r ≠ 0) : ∃ a : ℝ, v r = (a : ℂ) * (z x).val r := by
  apply phase_velocity_real_mul _ _ _ hr (diagonal_phase_equation (z x) d hd r)
  have he := congrArg (fun A : Matrix (Fin 3) (Fin 3) ℂ ↦ A r r)
    (sphere_curve_matrixVariation_conjugate z v x hz hv)
  rw [hd, Matrix.diagonal_mul, matrixVariation_diagonal] at he
  simpa [conjugate, matrixVariation_diagonal, star_mul, map_ofNat] using he

end Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary
