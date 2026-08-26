import ErdosProblems.Erdos1148.IntegralFormEmbedding

/-! # Primitive integral forms give optimal embeddings of the discriminant order -/

namespace Erdos1148.DukeArithmetic

theorem integral_form_preimage_coordinates {d : ℤ} {t : ℤ × ℤ × ℤ}
    (ht : discr t = d) (hprim : PrimitiveIntegralForm t) (w : QuadraticDiscrAlgebra d)
    (hw : integralFormFieldEmbedding ht w ∈ integralRationalMatrices) :
    ∃ x y : ℤ, w = (x : QuadraticDiscrAlgebra d) +
      (y : QuadraticDiscrAlgebra d) * quadraticOrderGenerator d := by
  obtain ⟨M, hM⟩ := (mem_integralRationalMatrices_iff _).mp hw
  rw [integralFormFieldEmbedding_apply] at hM
  have hm₀₀ := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℚ => A 0 0) hM
  have hm₀₁ := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℚ => A 0 1) hM
  have hm₁₀ := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℚ => A 1 0) hM
  have hm₁₁ := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℚ => A 1 1) hM
  change (M 0 0 : ℚ) = w.re - (t.2.1 : ℚ) * w.im at hm₀₀
  change (M 0 1 : ℚ) = -2 * (t.2.2 : ℚ) * w.im at hm₀₁
  change (M 1 0 : ℚ) = 2 * (t.1 : ℚ) * w.im at hm₁₀
  change (M 1 1 : ℚ) = w.re + (t.2.1 : ℚ) * w.im at hm₁₁
  have ha : (M 1 0 : ℚ) = (t.1 : ℚ) * (2 * w.im) := by linear_combination hm₁₀
  have hb : ((M 1 1 - M 0 0 : ℤ) : ℚ) = (t.2.1 : ℚ) * (2 * w.im) := by
    push_cast
    linear_combination hm₁₁ - hm₀₀
  have hc : ((-M 0 1 : ℤ) : ℚ) = (t.2.2 : ℚ) * (2 * w.im) := by
    push_cast
    linear_combination -hm₀₁
  obtain ⟨U, hU⟩ := hprim.integer_of_scaled_coefficients _ _ _ ha hb hc
  obtain ⟨k, hk⟩ := ht ▸ even_middle_sub_discr t
  have hkQ : (t.2.1 : ℚ) - d = (k : ℚ) + k := by exact_mod_cast hk
  refine ⟨M 0 0 + k * U, U, ?_⟩
  ext
  · simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.re_mul,
      QuadraticAlgebra.re_intCast, QuadraticAlgebra.im_intCast,
      quadraticOrderGenerator, zero_mul, mul_zero, add_zero]
    push_cast
    linear_combination -hm₀₀ - (t.2.1 : ℚ) / 2 * hU + (U : ℚ) / 2 * hkQ
  · simp only [QuadraticAlgebra.im_add, QuadraticAlgebra.im_mul,
      QuadraticAlgebra.re_intCast, QuadraticAlgebra.im_intCast,
      quadraticOrderGenerator, zero_mul, mul_zero, add_zero, zero_add]
    linarith

theorem primitive_form_embedding_optimal {d : ℤ} {t : ℤ × ℤ × ℤ}
    (ht : discr t = d) (hprim : PrimitiveIntegralForm t) :
    integralRationalMatrices.comap (integralFormFieldEmbedding ht).toRingHom =
      quadraticOrder d := by
  apply le_antisymm
  · intro w hw
    obtain ⟨x, y, rfl⟩ := integral_form_preimage_coordinates ht hprim w hw
    exact int_combination_mem_quadraticOrder d x y
  · exact quadraticOrder_le_integral_preimage ht

theorem mem_quadraticOrder_iff_coordinates {d : ℤ} {t : ℤ × ℤ × ℤ}
    (ht : discr t = d) (hprim : PrimitiveIntegralForm t) (w : QuadraticDiscrAlgebra d) :
    w ∈ quadraticOrder d ↔ ∃ x y : ℤ, w = (x : QuadraticDiscrAlgebra d) +
      (y : QuadraticDiscrAlgebra d) * quadraticOrderGenerator d := by
  constructor
  · intro hw
    exact integral_form_preimage_coordinates ht hprim w (quadraticOrder_le_integral_preimage ht hw)
  · rintro ⟨x, y, rfl⟩
    exact int_combination_mem_quadraticOrder d x y

end Erdos1148.DukeArithmetic
