import ErdosProblems.Erdos633b.RightTenthPolynomial

/-! The (pi/10, pi/5, 7pi/10) shape is excluded by the reflection root
and the negative conjugate, retaining the actual nonnegative boundary counts. -/

namespace Erdos633b.RightTenth

theorem nonnegative_even_coefficients_zero (a : ℝ) (ha : 0 < a) (u v : ℕ)
    (h : (u : ℝ) * a + v = 0) : u = 0 ∧ v = 0 := by
  have hu : (0 : ℝ) ≤ u := Nat.cast_nonneg u
  have hv : (0 : ℝ) ≤ v := Nat.cast_nonneg v
  have hz : (u : ℝ) = 0 := by nlinarith
  have hz' : (v : ℝ) = 0 := by rw [hz, zero_mul, zero_add] at h; exact h
  exact ⟨by exact_mod_cast hz, by exact_mod_cast hz'⟩

theorem Pair.double_seventh_impossible (P : Pair) (ha : 0 < P.a) (ha2 : P.a < 1 / 2)
    (hb : 0 < P.b) (n : ℕ) (hn : 0 < n) (m l : Fin 3 → ℕ)
    (h : (P.boundary m) ^ 2 = 2 * n * P.a ^ 2)
    (hs : P.boundary l = 2 * P.b * P.boundary m) : False := by
  obtain ⟨Q, hQb, _, hQsq⟩ := P.exists_negative ha ha2
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hr := P.transfer_square P.reflect n m h
  have hq := P.transfer_square Q n m h
  have hsr := P.transfer_double_side P.reflect m l hs
  have hsq := P.transfer_double_side Q m l hs
  have hprod : ((m 0 : ℝ) * P.a + m 2) * ((m 1 : ℝ) * P.b) = 0 := by
    dsimp only [Pair.boundary, Pair.reflect] at h hr
    linear_combination (1 / 4 : ℝ) * h - (1 / 4 : ℝ) * hr
  by_cases hm1 : m 1 = 0
  · have hl : (l 0 : ℝ) * P.a + l 2 = 0 := by
      dsimp only [Pair.boundary, Pair.reflect] at hs hsr
      simp only [hm1, Nat.cast_zero, zero_mul, add_zero] at hs hsr
      linear_combination (1 / 2 : ℝ) * hs + (1 / 2 : ℝ) * hsr
    obtain ⟨hl0, hl2⟩ := nonnegative_even_coefficients_zero P.a ha (l 0) (l 2) hl
    have hX : P.boundary m = (l 1 : ℝ) / 2 := by
      apply mul_left_cancel₀ hb.ne'
      simp only [Pair.boundary, hl0, hl2, Nat.cast_zero, zero_mul, zero_add, add_zero] at hs
      dsimp only [Pair.boundary]
      linear_combination -(1 / 2 : ℝ) * hs
    have hXq : Q.boundary m = (l 1 : ℝ) / 2 := by
      apply mul_left_cancel₀ hQb.ne'
      simp only [Pair.boundary, hl0, hl2, Nat.cast_zero, zero_mul, zero_add, add_zero] at hsq
      dsimp only [Pair.boundary]
      linear_combination -(1 / 2 : ℝ) * hsq
    rw [hX] at h
    rw [hXq] at hq
    have hpos : 0 < (n : ℝ) * (Q.a ^ 2 - P.a ^ 2) := mul_pos hn' (sub_pos.mpr hQsq)
    nlinarith
  · have hV : 0 < (m 1 : ℝ) * P.b := mul_pos (by exact_mod_cast Nat.pos_of_ne_zero hm1) hb
    have hU := (mul_eq_zero.mp hprod).resolve_right hV.ne'
    obtain ⟨hm0, hm2⟩ := nonnegative_even_coefficients_zero P.a ha (m 0) (m 2) hU
    have he : ((m 1 : ℝ) ^ 2 + 2 * n) * (P.b ^ 2 - Q.b ^ 2) = 0 := by
      simp only [Pair.boundary, hm0, hm2, Nat.cast_zero, zero_mul, zero_add, add_zero] at h hq
      linear_combination h - hq + 2 * (n : ℝ) * (P.unit - Q.unit)
    have hc : 0 < (m 1 : ℝ) ^ 2 + 2 * n := by positivity
    have hdiff : 0 < P.b ^ 2 - Q.b ^ 2 := by linarith [P.unit, Q.unit]
    exact (mul_pos hc hdiff).ne' he

end Erdos633b.RightTenth
