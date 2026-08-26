import ErdosProblems.Erdos1148.FormAction

/-! # Primitive integral forms via a Bézout relation between their coefficients -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

def PrimitiveIntegralForm (t : ℤ × ℤ × ℤ) : Prop :=
  ∃ x y z : ℤ, x * t.1 + y * t.2.1 + z * t.2.2 = 1

lemma primitiveIntegralForm_of_monic {t : ℤ × ℤ × ℤ} (ht : t.1 = 1) :
    PrimitiveIntegralForm t := ⟨1, 0, 0, by simp [ht]⟩

lemma primitiveIntegralForm_of_transform (M : Matrix (Fin 2) (Fin 2) ℤ)
    {t : ℤ × ℤ × ℤ} (ht : PrimitiveIntegralForm (transform M t)) : PrimitiveIntegralForm t := by
  obtain ⟨x, y, z, h⟩ := ht
  refine ⟨x * M 0 0 ^ 2 + y * (2 * M 0 0 * M 0 1) + z * M 0 1 ^ 2,
    x * M 0 0 * M 1 0 + y * (M 0 0 * M 1 1 + M 0 1 * M 1 0) + z * M 0 1 * M 1 1,
    x * M 1 0 ^ 2 + y * (2 * M 1 0 * M 1 1) + z * M 1 1 ^ 2, ?_⟩
  dsimp [transform] at h
  linear_combination h

lemma primitiveIntegralForm_formAction_iff (g : SL(2, ℤ)) (t : ℤ × ℤ × ℤ) :
    PrimitiveIntegralForm (formAction g t) ↔ PrimitiveIntegralForm t := by
  constructor
  · exact primitiveIntegralForm_of_transform (g⁻¹ : SL(2, ℤ))
  · intro ht
    apply primitiveIntegralForm_of_transform (g : Matrix (Fin 2) (Fin 2) ℤ)
    have hi : PrimitiveIntegralForm (formAction g⁻¹ (formAction g t)) := by
      rw [← formAction_mul, inv_mul_cancel, formAction_one]
      exact ht
    simpa only [formAction, inv_inv] using hi

lemma PrimitiveIntegralForm.integer_of_scaled_coefficients {R : Type*} [CommRing R]
    {t : ℤ × ℤ × ℤ} (ht : PrimitiveIntegralForm t) {u : R} (a b c : ℤ)
    (ha : (a : R) = t.1 * u) (hb : (b : R) = t.2.1 * u) (hc : (c : R) = t.2.2 * u) :
    ∃ v : ℤ, (v : R) = u := by
  obtain ⟨x, y, z, h⟩ := ht
  refine ⟨x * a + y * b + z * c, ?_⟩
  have hR : (x : R) * t.1 + (y : R) * t.2.1 + (z : R) * t.2.2 = 1 := by
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_one] using
      congrArg (fun n : ℤ => (n : R)) h
  push_cast
  rw [ha, hb, hc]
  linear_combination u * hR

end Erdos1148.DukeArithmetic
