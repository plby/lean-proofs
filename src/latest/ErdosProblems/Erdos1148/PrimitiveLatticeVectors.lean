import ErdosProblems.Erdos1148.LatticeShortVectorUniqueness
import Mathlib.RingTheory.Coprime.Lemmas

/-! # Primitive integral vectors give the shortest vector in their direction -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

theorem exists_primitive_integer_pair {u v : ℤ} (huv : u ≠ 0 ∨ v ≠ 0) :
    ∃ k a b : ℤ, 0 < k ∧ IsCoprime a b ∧ u = k * a ∧ v = k * b := by
  have hgpos : 0 < Int.gcd u v := Int.gcd_pos_iff.mpr huv
  obtain ⟨a, b, hab, ha, hb⟩ := Int.exists_gcd_one hgpos
  refine ⟨Int.gcd u v, a, b, by exact_mod_cast hgpos, Int.isCoprime_iff_gcd_eq_one.mpr hab,
    ?_, ?_⟩
  · simpa only [mul_comm] using ha
  · simpa only [mul_comm] using hb

theorem integer_pair_multiple_of_primitive {u v w z : ℤ} (huv : IsCoprime u v)
    (hdet : u * z - v * w = 0) : ∃ k : ℤ, w = k * u ∧ z = k * v := by
  obtain ⟨a, b, hab⟩ := huv
  refine ⟨a * w + b * z, ?_, ?_⟩
  · linear_combination -w * hab - b * hdet
  · linear_combination -z * hab + a * hdet

lemma modularVectorLengthSq_mul_pair (g : SL(2, ℝ)) (k u v : ℤ) :
    modularVectorLengthSq g (k * u) (k * v) = (k : ℝ) ^ 2 * modularVectorLengthSq g u v := by
  simp only [modularVectorLengthSq, modularVector, Int.cast_mul]
  ring

theorem primitive_vector_lengthSq_le (g : SL(2, ℝ)) {u v w z : ℤ}
    (huv : IsCoprime u v) (hwz : w ≠ 0 ∨ z ≠ 0) (hdet : u * z - v * w = 0) :
    modularVectorLengthSq g u v ≤ modularVectorLengthSq g w z := by
  obtain ⟨k, rfl, rfl⟩ := integer_pair_multiple_of_primitive huv hdet
  have hk : k ≠ 0 := by intro h; simp only [h, zero_mul, ne_eq, not_true_eq_false, or_self] at hwz
  have hkZ : (1 : ℤ) ≤ k ^ 2 := by have := sq_pos_of_ne_zero hk; omega
  have hkR : (1 : ℝ) ≤ (k : ℝ) ^ 2 := by exact_mod_cast hkZ
  rw [modularVectorLengthSq_mul_pair]
  exact le_mul_of_one_le_left (by dsimp [modularVectorLengthSq]; positivity) hkR

theorem mem_modularCusp_iff_primitive (g : SL(2, ℝ)) (H : ℝ) :
    modularMk g ∈ modularCusp H ↔
      ∃ u v : ℤ, IsCoprime u v ∧ modularVectorLengthSq g u v < (H ^ 2)⁻¹ := by
  rw [mem_modularCusp_iff_representative]
  constructor
  · rintro ⟨u, v, huv, hshort⟩
    obtain ⟨k, a, b, hk, hab, ha, hb⟩ := exists_primitive_integer_pair huv
    refine ⟨a, b, hab, ?_⟩
    apply (primitive_vector_lengthSq_le g hab huv ?_).trans_lt hshort
    rw [ha, hb]
    ring
  · rintro ⟨u, v, huv, hshort⟩
    exact ⟨u, v, huv.ne_zero_or_ne_zero, hshort⟩

end Erdos1148.DukeArithmetic
