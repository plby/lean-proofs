import ErdosProblems.Erdos1148.IntegralVectorLattice

/-! # The cyclic-vector coordinates of the quadratic-field representation -/

namespace Erdos1148.DukeArithmetic

noncomputable def formLatticeCoordinates {d : ℤ} (t : ℤ × ℤ × ℤ) (ha : t.1 ≠ 0) :
    QuadraticDiscrAlgebra d ≃ₗ[ℚ] (Fin 2 → ℚ) where
  toFun w := ![w.re - (t.2.1 : ℚ) * w.im, 2 * (t.1 : ℚ) * w.im]
  invFun v := ⟨v 0 + (t.2.1 : ℚ) * (v 1 / (2 * (t.1 : ℚ))), v 1 / (2 * (t.1 : ℚ))⟩
  left_inv w := by
    have haQ : (t.1 : ℚ) ≠ 0 := by exact_mod_cast ha
    ext <;> dsimp <;> field_simp <;> ring
  right_inv v := by
    have haQ : (t.1 : ℚ) ≠ 0 := by exact_mod_cast ha
    ext i
    fin_cases i <;> dsimp <;> field_simp <;> ring
  map_add' w z := by ext i; fin_cases i <;> dsimp <;> ring
  map_smul' c w := by ext i; fin_cases i <;> dsimp <;> ring

lemma formLatticeCoordinates_eq_firstColumn {d : ℤ} {t : ℤ × ℤ × ℤ}
    (ht : discr t = d) (ha : t.1 ≠ 0) (w : QuadraticDiscrAlgebra d) :
    formLatticeCoordinates t ha w = fun i => integralFormFieldEmbedding ht w i 0 := by
  rw [integralFormFieldEmbedding_apply]
  ext i
  fin_cases i <;> rfl

lemma formLatticeCoordinates_mul {d : ℤ} {t : ℤ × ℤ × ℤ}
    (ht : discr t = d) (ha : t.1 ≠ 0) (w z : QuadraticDiscrAlgebra d) :
    formLatticeCoordinates t ha (w * z) =
      (integralFormFieldEmbedding ht w).mulVec (formLatticeCoordinates t ha z) := by
  rw [formLatticeCoordinates_eq_firstColumn ht, map_mul,
    formLatticeCoordinates_eq_firstColumn ht]
  rfl

end Erdos1148.DukeArithmetic
