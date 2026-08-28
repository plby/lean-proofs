import Mathlib.LinearAlgebra.Matrix.Transvection

/-! # Column addition and its explicit inverse over the integers -/

open Function

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

theorem mul_transvection_surjective {r n : ℕ} (A : Matrix (Fin r) (Fin n) ℤ)
    (i j : Fin n) (hij : i ≠ j) (k : ℤ) (hA : Surjective A.mulVec) :
    Surjective (A * Matrix.transvection i j k).mulVec := by
  intro y
  obtain ⟨z, hz⟩ := hA y
  refine ⟨(Matrix.transvection i j (-k)).mulVec z, ?_⟩
  rw [Matrix.mulVec_mulVec, Matrix.mul_assoc,
    Matrix.transvection_mul_transvection_same i j hij, add_neg_cancel,
    Matrix.transvection_zero, Matrix.mul_one]
  exact hz

theorem eq_mul_transvection_of_columns {r n : ℕ} (A A' : Matrix (Fin r) (Fin n) ℤ)
    (i j : Fin n) (k : ℤ) (hchanged : ∀ u, A' u j = A u j + k * A u i)
    (hother : ∀ u v, v ≠ j → A' u v = A u v) : A' = A * Matrix.transvection i j k := by
  funext u v
  by_cases hv : v = j
  · subst v
    exact (hchanged u).trans (Matrix.mul_transvection_apply_same i j u k A).symm
  · exact (hother u v hv).trans (Matrix.mul_transvection_apply_of_ne i j u v hv k A).symm

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
