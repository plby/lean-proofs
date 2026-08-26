import ErdosProblems.Erdos1148.ConjugateFormIdeal

/-! # The fractional ideal of a primitive form is invertible -/

namespace Erdos1148.DukeArithmetic

open scoped nonZeroDivisors

lemma int_mul_mem_orderFractionalIdeal {d : ℤ} [Fact (¬IsSquare d)]
    (I : FractionalIdeal (quadraticOrder d)⁰ (QuadraticDiscrAlgebra d)) (n : ℤ)
    {z : QuadraticDiscrAlgebra d} (hz : z ∈ I) : (n : QuadraticDiscrAlgebra d) * z ∈ I :=
  (I : Submodule (quadraticOrder d) (QuadraticDiscrAlgebra d)).smul_mem
    (n : quadraticOrder d) hz

theorem formFractionalIdeal_mul_conjugate {d : ℤ} [Fact (¬IsSquare d)]
    {t : ℤ × ℤ × ℤ} (ht : discr t = d) (hprim : PrimitiveIntegralForm t) (ha : t.1 ≠ 0) :
    formFractionalIdeal ht ha * formFractionalIdeal ((discr_conjugateForm t).trans ht) ha =
      FractionalIdeal.spanSingleton (quadraticOrder d)⁰ (t.1 : QuadraticDiscrAlgebra d)⁻¹ := by
  let I := formFractionalIdeal ht ha
  let J := formFractionalIdeal ((discr_conjugateForm t).trans ht) ha
  let P := I * J
  have haK : (t.1 : QuadraticDiscrAlgebra d) ≠ 0 := Int.cast_ne_zero.mpr ha
  apply le_antisymm
  · apply FractionalIdeal.mul_le.mpr
    intro v hv w hw
    apply (FractionalIdeal.mem_spanSingleton _).mpr
    refine ⟨⟨(t.1 : QuadraticDiscrAlgebra d) * v * w,
      leading_mul_formIdeal_product_mem_order ht ha hv hw⟩, ?_⟩
    change ((t.1 : QuadraticDiscrAlgebra d) * v * w) * (t.1 : QuadraticDiscrAlgebra d)⁻¹ = v * w
    field_simp
  · apply FractionalIdeal.spanSingleton_le_iff_mem.mpr
    have h1 : (1 : QuadraticDiscrAlgebra d) ∈ P := by
      simpa only [one_mul] using FractionalIdeal.mul_mem_mul
        (one_mem_formFractionalIdeal ht ha)
        (one_mem_formFractionalIdeal ((discr_conjugateForm t).trans ht) ha)
    have hβ : formIdealGenerator (d := d) t ∈ P := by
      simpa only [mul_one] using FractionalIdeal.mul_mem_mul
        (show formIdealGenerator t ∈ I from formIdealGenerator_mem t ha)
        (one_mem_formFractionalIdeal ((discr_conjugateForm t).trans ht) ha)
    have hβ' : formIdealGenerator (d := d) (conjugateForm t) ∈ P := by
      simpa only [one_mul] using FractionalIdeal.mul_mem_mul (one_mem_formFractionalIdeal ht ha)
        (show formIdealGenerator (conjugateForm t) ∈ J from
          formIdealGenerator_mem (conjugateForm t) ha)
    have hββ' : formIdealGenerator (d := d) t * formIdealGenerator (conjugateForm t) ∈ P :=
      FractionalIdeal.mul_mem_mul (show formIdealGenerator t ∈ I from formIdealGenerator_mem t ha)
        (show formIdealGenerator (conjugateForm t) ∈ J from
          formIdealGenerator_mem (conjugateForm t) ha)
    obtain ⟨x, y, z, hbez⟩ := hprim
    let v : QuadraticDiscrAlgebra d := (x : QuadraticDiscrAlgebra d) +
      (y : QuadraticDiscrAlgebra d) * (formIdealGenerator t -
        formIdealGenerator (conjugateForm t)) - (z : QuadraticDiscrAlgebra d) *
          (formIdealGenerator t * formIdealGenerator (conjugateForm t))
    let L : Submodule (quadraticOrder d) (QuadraticDiscrAlgebra d) := P
    have hv : v ∈ P := by
      apply L.sub_mem
      · apply L.add_mem
        · change (x : QuadraticDiscrAlgebra d) ∈ P
          simpa only [mul_one] using int_mul_mem_orderFractionalIdeal P x h1
        · exact int_mul_mem_orderFractionalIdeal P y (L.sub_mem hβ hβ')
      · exact int_mul_mem_orderFractionalIdeal P z hββ'
    have hbezK : (x : QuadraticDiscrAlgebra d) * (t.1 : QuadraticDiscrAlgebra d) +
        (y : QuadraticDiscrAlgebra d) * (t.2.1 : QuadraticDiscrAlgebra d) +
        (z : QuadraticDiscrAlgebra d) * (t.2.2 : QuadraticDiscrAlgebra d) = 1 := by
      simpa only [Int.cast_add, Int.cast_mul, Int.cast_one] using
        congrArg (fun n : ℤ => (n : QuadraticDiscrAlgebra d)) hbez
    have hmul : (t.1 : QuadraticDiscrAlgebra d) * v = 1 := by
      calc
        _ = (x : QuadraticDiscrAlgebra d) * (t.1 : QuadraticDiscrAlgebra d) +
            (y : QuadraticDiscrAlgebra d) * ((t.1 : QuadraticDiscrAlgebra d) *
              (formIdealGenerator t - formIdealGenerator (conjugateForm t))) -
            (z : QuadraticDiscrAlgebra d) * ((t.1 : QuadraticDiscrAlgebra d) *
              formIdealGenerator t * formIdealGenerator (conjugateForm t)) := by dsimp [v]; ring
        _ = 1 := by
          rw [leading_mul_generator_difference t ha, leading_mul_generator_product ht ha]
          linear_combination hbezK
    have heq : v = (t.1 : QuadraticDiscrAlgebra d)⁻¹ := by
      apply mul_left_cancel₀ haK
      rw [hmul, mul_inv_cancel₀ haK]
    rw [← heq]
    exact hv

theorem formFractionalIdeal_isUnit {d : ℤ} [Fact (¬IsSquare d)]
    {t : ℤ × ℤ × ℤ} (ht : discr t = d) (hprim : PrimitiveIntegralForm t) (ha : t.1 ≠ 0) :
    IsUnit (formFractionalIdeal ht ha) := by
  let J := FractionalIdeal.spanSingleton (quadraticOrder d)⁰ (t.1 : QuadraticDiscrAlgebra d) *
    formFractionalIdeal ((discr_conjugateForm t).trans ht) ha
  have hmul : formFractionalIdeal ht ha * J = 1 := by
    dsimp [J]
    rw [mul_left_comm, formFractionalIdeal_mul_conjugate ht hprim ha,
      FractionalIdeal.spanSingleton_mul_spanSingleton, mul_inv_cancel₀ (Int.cast_ne_zero.mpr ha),
      FractionalIdeal.spanSingleton_one]
  exact ⟨⟨formFractionalIdeal ht ha, J, hmul, by rw [mul_comm]; exact hmul⟩, rfl⟩

end Erdos1148.DukeArithmetic
