import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicAngularKernel

/-! # Tangency identities for actual symmetric unitary matrix curves -/

noncomputable section

open scoped Matrix

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicBottMatrix

open QuaternionicSymmetricMatrices ComplexCrossProductUnitary

theorem symmetric_curve_derivative (B : ℝ → Space (Fin 3))
    (D : Matrix (Fin 3) (Fin 3) ℂ) (x : ℝ)
    (hB : ∀ r s, HasDerivAt (fun y ↦ (B y).val.val r s) (D r s) x) (r s : Fin 3) :
    D r s = D s r := by
  have he := hB s r
  have hf : (fun y ↦ (B y).val.val s r) = fun y ↦ (B y).val.val r s := by
    funext y
    exact symmetric_entry (B y) s r
  rw [hf] at he
  exact (hB r s).unique he

theorem unitary_curve_derivative (B : ℝ → Space (Fin 3))
    (D : Matrix (Fin 3) (Fin 3) ℂ) (x : ℝ)
    (hB : ∀ r s, HasDerivAt (fun y ↦ (B y).val.val r s) (D r s) x) (r s : Fin 3) :
    ∑ k, (star (D k r) * (B x).val.val k s + star ((B x).val.val k r) * D k s) = 0 := by
  have he := HasDerivAt.fun_sum (u := Finset.univ)
    (fun k (_ : k ∈ Finset.univ) ↦ (hB k r).star.mul (hB k s))
  have hf : (fun y : ℝ ↦ ∑ k, ((fun y ↦ star ((B y).val.val k r)) *
      (fun y ↦ (B y).val.val k s)) y) =
      fun _ ↦ (1 : Matrix (Fin 3) (Fin 3) ℂ) r s := by
    funext y
    exact congrArg (fun A : Matrix (Fin 3) (Fin 3) ℂ ↦ A r s)
      (Unitary.coe_star_mul_self (B y).val)
  rw [hf] at he
  exact he.unique (hasDerivAt_const x _)

def midpointDetVariation (u : ℂ) (D : Matrix (Fin 3) (Fin 3) ℂ) : ℂ :=
  u ^ 2 * (targetAlpha * (D 0 0 + D 2 2) - targetBeta * (D 0 2 + D 2 0) - D 1 1)

theorem hasDerivAt_det_midpoint (B : ℝ → Space (Fin 3))
    (D : Matrix (Fin 3) (Fin 3) ℂ) (x : ℝ)
    (hB : ∀ r s, HasDerivAt (fun y ↦ (B y).val.val r s) (D r s) x)
    (u : ℂ) (hBx : (B x).val.val = u • targetMatrix targetAlpha targetBeta) :
    HasDerivAt (fun y ↦ (B y).val.val.det) (midpointDetVariation u D) x := by
  have he := (((((hB 0 0).mul (hB 1 1)).mul (hB 2 2)).sub
    (((hB 0 0).mul (hB 1 2)).mul (hB 2 1))).sub
    (((hB 0 1).mul (hB 1 0)).mul (hB 2 2))).add
    (((hB 0 1).mul (hB 1 2)).mul (hB 2 0))
  have he' := (he.add (((hB 0 2).mul (hB 1 0)).mul (hB 2 1))).sub
    (((hB 0 2).mul (hB 1 1)).mul (hB 2 0))
  convert he' using 1 <;> try rfl
  · funext y
    simp only [Matrix.det_fin_three, Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
  · simp [Pi.mul_apply, hBx, targetMatrix,
      midpointDetVariation, Matrix.cons_val_two]
    linear_combination -(u ^ 2 * D 1 1) * target_polynomial

theorem constant_curve_det_tangent_midpoint (B : ℝ → Space (Fin 3))
    (D : Matrix (Fin 3) (Fin 3) ℂ) (x : ℝ)
    (hB : ∀ r s, HasDerivAt (fun y ↦ (B y).val.val r s) (D r s) x)
    (c : ℂ) (hdet : ∀ y, (B y).val.val.det = c) (u : unitary ℂ)
    (hBx : (B x).val.val = u.val • targetMatrix targetAlpha targetBeta) :
    targetAlpha * (D 0 0 + D 2 2) - targetBeta * (D 0 2 + D 2 0) - D 1 1 = 0 := by
  have he := hasDerivAt_det_midpoint B D x hB u.val hBx
  have hf : (fun y ↦ (B y).val.val.det) = fun _ ↦ c := funext hdet
  rw [hf] at he
  have hz := he.unique (hasDerivAt_const x c)
  exact (mul_eq_zero.mp hz).resolve_left (pow_ne_zero 2 (unitary_complex_ne_zero u))

theorem special_curve_det_tangent_midpoint (B : ℝ → Space (Fin 3))
    (D : Matrix (Fin 3) (Fin 3) ℂ) (x : ℝ)
    (hB : ∀ r s, HasDerivAt (fun y ↦ (B y).val.val r s) (D r s) x)
    (hdet : ∀ y, (B y).val.val.det = 1) (u : unitary ℂ)
    (hBx : (B x).val.val = u.val • targetMatrix targetAlpha targetBeta) :
    targetAlpha * (D 0 0 + D 2 2) - targetBeta * (D 0 2 + D 2 0) - D 1 1 = 0 :=
  constant_curve_det_tangent_midpoint B D x hB 1 hdet u hBx

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicBottMatrix
