import Mathlib

/-!
# Uniform coefficients after recentering an affine progression

Bounds on two endpoint values control the slope and the recentered
constant coefficient. This makes polynomial-size hypotheses uniform in
the varying affine progressions used by the quadratic encodings.
-/

open scoped BigOperators

namespace Erdos587

lemma affine_slope_span_le {A B : ℤ} {X Y : ℕ} (hY : 2 ≤ Y)
    (hfirst : (A + B).natAbs ≤ X) (hlast : (A + B * Y).natAbs ≤ X) :
    B.natAbs * (Y - 1) ≤ 2 * X := by
  have heq : A + B * Y - (A + B) = B * (Y - 1 : ℕ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ Y)]
    push_cast
    ring
  have h := Int.natAbs_sub_le (A + B * Y) (A + B)
  rw [heq, Int.natAbs_mul, Int.natAbs_natCast] at h
  omega

lemma affine_slope_length_le {A B : ℤ} {X Y : ℕ} (hY : 2 ≤ Y)
    (hfirst : (A + B).natAbs ≤ X) (hlast : (A + B * Y).natAbs ≤ X) :
    B.natAbs * Y ≤ 4 * X := by
  have hspan := affine_slope_span_le hY hfirst hlast
  have hYspan : Y ≤ 2 * (Y - 1) := by omega
  have hmul := Nat.mul_le_mul_left B.natAbs hYspan
  nlinarith

lemma affine_coefficients_le {A B : ℤ} {X Y : ℕ} (hY : 2 ≤ Y)
    (hfirst : (A + B).natAbs ≤ X) (hlast : (A + B * Y).natAbs ≤ X) :
    B.natAbs ≤ 2 * X ∧ A.natAbs ≤ 3 * X ∧ (A - B * Y).natAbs ≤ 7 * X := by
  have hspan := affine_slope_span_le hY hfirst hlast
  have hlength := affine_slope_length_le hY hfirst hlast
  have hB : B.natAbs ≤ 2 * X := by
    have hmul := Nat.mul_le_mul_left B.natAbs (by omega : 1 ≤ Y - 1)
    nlinarith
  have hA : A.natAbs ≤ 3 * X := by
    have h := Int.natAbs_sub_le (A + B) B
    rw [add_sub_cancel_right] at h
    omega
  refine ⟨hB, hA, ?_⟩
  have h := Int.natAbs_sub_le A (B * Y)
  rw [Int.natAbs_mul, Int.natAbs_natCast] at h
  omega

lemma affine_recenter_value (A B : ℤ) (Y t : ℕ) :
    (A - B * Y) + B * (Y + t : ℕ) = A + B * t := by
  push_cast
  ring

lemma affine_recenter_coprime {A B : ℤ} (hcop : IsCoprime A B) (Y : ℕ) :
    IsCoprime (A - B * Y) B := by
  simpa only [mul_neg, sub_eq_add_neg] using hcop.add_mul_left_left (-(Y : ℤ))

/-- Reindexing into `(Y,2Y]` preserves the exact finite sum. -/
theorem sum_affine_recenter (f : ℤ → ℝ) (A B : ℤ) (Y : ℕ) :
    (∑ t ∈ Finset.Icc 1 Y, f (A + B * t)) =
      ∑ j ∈ Finset.Ioc Y (2 * Y), f ((A - B * Y) + B * j) := by
  apply Finset.sum_bij (fun t _ => Y + t)
  · intro t ht
    obtain ⟨ht1, htY⟩ := Finset.mem_Icc.mp ht
    exact Finset.mem_Ioc.mpr (by omega)
  · intro t ht s hs heq
    omega
  · intro j hj
    obtain ⟨hYj, hjY⟩ := Finset.mem_Ioc.mp hj
    refine ⟨j - Y, Finset.mem_Icc.mpr (by omega), by omega⟩
  · intro t ht
    rw [affine_recenter_value]

end Erdos587
