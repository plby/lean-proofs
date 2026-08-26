import ErdosProblems.Erdos1148.QuadraticOrderIntegers

/-! # Units of the discriminant order from integral Pell coordinates -/

namespace Erdos1148.DukeArithmetic

noncomputable def pellQuadraticElement (d T U : ℤ) : QuadraticDiscrAlgebra d :=
  ⟨(T : ℚ) / 2, (U : ℚ) / 2⟩

theorem pellQuadraticElement_mem_order (d T U : ℤ) (hpar : Even (T - d * U)) :
    pellQuadraticElement d T U ∈ quadraticOrder d := by
  obtain ⟨k, hk⟩ := hpar
  have hkQ : (T : ℚ) - (d : ℚ) * U = (k : ℚ) + k := by exact_mod_cast hk
  have heq : pellQuadraticElement d T U =
      (k : QuadraticDiscrAlgebra d) +
        (U : QuadraticDiscrAlgebra d) * quadraticOrderGenerator d := by
    ext <;> simp [pellQuadraticElement, quadraticOrderGenerator] <;> linarith
  rw [heq]
  exact int_combination_mem_quadraticOrder d k U

lemma pellParity_neg_right (d T U : ℤ) (hpar : Even (T - d * U)) : Even (T - d * (-U)) := by
  obtain ⟨k, hk⟩ := hpar
  refine ⟨k + d * U, ?_⟩
  linear_combination hk

lemma pellQuadraticElement_mul_conjugate (d T U : ℤ) (hpell : T ^ 2 - d * U ^ 2 = 4) :
    pellQuadraticElement d T U * pellQuadraticElement d T (-U) = 1 := by
  have hpQ : (T : ℚ) ^ 2 - (d : ℚ) * (U : ℚ) ^ 2 = 4 := by exact_mod_cast hpell
  ext <;> simp [pellQuadraticElement, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  · linear_combination hpQ / 4
  · ring

noncomputable def pellOrderUnit (d T U : ℤ) (hpell : T ^ 2 - d * U ^ 2 = 4)
    (hpar : Even (T - d * U)) : (quadraticOrder d)ˣ where
  val := ⟨pellQuadraticElement d T U, pellQuadraticElement_mem_order d T U hpar⟩
  inv := ⟨pellQuadraticElement d T (-U),
    pellQuadraticElement_mem_order d T (-U) (pellParity_neg_right d T U hpar)⟩
  val_inv := Subtype.ext (pellQuadraticElement_mul_conjugate d T U hpell)
  inv_val := by
    apply Subtype.ext
    change pellQuadraticElement d T (-U) * pellQuadraticElement d T U = 1
    rw [mul_comm]
    exact pellQuadraticElement_mul_conjugate d T U hpell

lemma pellOrderUnit_val (d T U : ℤ) (hpell : T ^ 2 - d * U ^ 2 = 4)
    (hpar : Even (T - d * U)) :
    ((pellOrderUnit d T U hpell hpar : quadraticOrder d) : QuadraticDiscrAlgebra d) =
      pellQuadraticElement d T U := rfl

end Erdos1148.DukeArithmetic
