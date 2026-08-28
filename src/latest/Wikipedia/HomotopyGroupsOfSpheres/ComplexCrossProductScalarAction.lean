import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicMidpointSeed

/-! # Cube-root scalar symmetries of the explicit symmetric map -/

noncomputable section

open scoped Matrix

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary

open QuaternionicBottMatrix

def sphereOfNormPolynomial (v : Vector) (hv : normPolynomial v = 1) : UnitSphere :=
  ⟨WithLp.toLp 2 v, by
    apply mem_sphere_zero_iff_norm.mpr
    have he := normPolynomial_eq_norm_sq (WithLp.toLp 2 v)
    change normPolynomial v = _ at he
    rw [hv] at he
    have hs : ‖WithLp.toLp 2 v‖ ^ 2 = (1 : ℝ) := by exact_mod_cast he.symm
    nlinarith [norm_nonneg (WithLp.toLp 2 v)]⟩

theorem normPolynomial_unitary_smul (q : unitary ℂ) (z : Vector) :
    normPolynomial (q.val • z) = normPolynomial z := by
  calc
    _ = (star q.val * q.val) * normPolynomial z := by
      simp [normPolynomial, Fin.sum_univ_three, star_mul]
      ring
    _ = _ := by rw [q.property.1, one_mul]

def scalarSphere (q : unitary ℂ) (z : UnitSphere) : UnitSphere :=
  sphereOfNormPolynomial (q.val • z.val) (by
    rw [normPolynomial_unitary_smul, normPolynomial_unit])

theorem scalarSphere_val (q : unitary ℂ) (z : UnitSphere) (r : Fin 3) :
    (scalarSphere q z).val r = q.val * z.val r := rfl

theorem scalarSphere_injective (q : unitary ℂ) : Function.Injective (scalarSphere q) := by
  intro z w h
  apply Subtype.ext
  ext r
  apply mul_left_cancel₀ (unitary_complex_ne_zero q)
  exact congrArg (fun v : UnitSphere ↦ v.val r) h

theorem cube_one_star (q : unitary ℂ) (hq : q.val ^ 3 = 1) : star q.val = q.val ^ 2 := by
  calc
    star q.val = q.val ^ 3 * star q.val := by rw [hq, one_mul]
    _ = q.val ^ 2 * (q.val * star q.val) := by ring
    _ = _ := by rw [q.property.2, mul_one]

theorem matrix_cube_one_smul (q : unitary ℂ) (hq : q.val ^ 3 = 1) (z : Vector) :
    matrix (q.val • z) = q.val ^ 2 • matrix z := by
  have hc : (starRingEnd ℂ) q.val = q.val ^ 2 := cube_one_star q hq
  ext r s
  fin_cases r <;> fin_cases s <;>
    simp [matrix, outer, crossMatrix, Matrix.cons_val_two, hc] <;> ring

theorem symmetricMap_scalarSphere (q : unitary ℂ) (hq : q.val ^ 3 = 1) (z : UnitSphere) :
    (symmetricMap (scalarSphere q z)).val.val = q.val • (symmetricMap z).val.val := by
  rw [symmetricMap_val, symmetricMap_val]
  change matrix (q.val • z.val) * (matrix (q.val • z.val)).transpose = _
  rw [matrix_cube_one_smul q hq, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul]
  have h : q.val ^ 2 * q.val ^ 2 = q.val := by
    calc
      _ = q.val ^ 3 * q.val := by ring
      _ = _ := by rw [hq, one_mul]
  rw [h]

end Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary
