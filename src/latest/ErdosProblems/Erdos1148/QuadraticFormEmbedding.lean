import ErdosProblems.Erdos1148.QuadraticOrderField

/-! # The matrix embedding associated with a binary quadratic form -/

namespace Erdos1148.DukeArithmetic

def formRootMatrix {R : Type*} [CommRing R] (t : R × R × R) : Matrix (Fin 2) (Fin 2) R :=
  pellFormMatrix t 0 1

lemma formRootMatrix_sq {R : Type*} [CommRing R] (t : R × R × R) :
    formRootMatrix t * formRootMatrix t = discr t • (1 : Matrix (Fin 2) (Fin 2) R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [formRootMatrix, pellFormMatrix, Matrix.mul_apply, Fin.sum_univ_two, discr] <;> ring

noncomputable def quadraticFormEmbedding {R : Type*} [CommRing R] {d : R}
    {t : R × R × R} (ht : discr t = d) :
    QuadraticAlgebra R d 0 →ₐ[R] Matrix (Fin 2) (Fin 2) R :=
  QuadraticAlgebra.lift ⟨formRootMatrix t, by
    rw [zero_smul, add_zero, ← ht]
    exact formRootMatrix_sq t⟩

lemma quadraticFormEmbedding_apply {R : Type*} [CommRing R] {d : R}
    {t : R × R × R} (ht : discr t = d) (w : QuadraticAlgebra R d 0) :
    quadraticFormEmbedding ht w = pellFormMatrix t w.re w.im := by
  change w.re • (1 : Matrix (Fin 2) (Fin 2) R) + w.im • formRootMatrix t = _
  ext i j
  fin_cases i <;> fin_cases j <;> simp [formRootMatrix, pellFormMatrix] <;> ring

lemma quadraticFormEmbedding_injective {d : ℤ} [Fact (¬IsSquare d)]
    {t : ℚ × ℚ × ℚ} (ht : discr t = (d : ℚ)) :
    Function.Injective (quadraticFormEmbedding ht) :=
  (quadraticFormEmbedding ht).injective

end Erdos1148.DukeArithmetic
