import ErdosProblems.Erdos633b.AngleDeterminant

/-! Positive common natural angle weights extracted from exact signed
integer elimination identities. Absolute values handle both determinant signs. -/

namespace Erdos633b.Triangle

theorem integer_angle_weights_of_scaled (S : Triangle) (D : ℤ) (hD : D ≠ 0)
    (v : Fin 3 → ℤ) (he : ∀ i, (D : ℝ) * S.angle i = (v i : ℝ) * Real.pi) :
    3 ≤ D.natAbs ∧ ∃ w : Fin 3 → ℕ,
      (∀ i, S.angle i = (w i : ℝ) * (Real.pi / D.natAbs)) ∧
      (∀ i, 0 < w i ∧ w i < D.natAbs) ∧ ∑ i, w i = D.natAbs := by
  let w : Fin 3 → ℕ := fun i => (v i).natAbs
  have hDr : (D : ℝ) ≠ 0 := by exact_mod_cast hD
  have hN : (0 : ℝ) < D.natAbs := by
    simpa only [Nat.cast_natAbs, Int.cast_abs] using abs_pos.mpr hDr
  have hi (i : Fin 3) : (D.natAbs : ℝ) * S.angle i = (w i : ℝ) * Real.pi := by
    simpa only [w, Nat.cast_natAbs, Int.cast_abs, abs_mul,
      abs_of_pos (S.angle_pos i), abs_of_pos Real.pi_pos] using congrArg abs (he i)
  have hwp (i : Fin 3) : 0 < w i := by
    have hp : 0 < (w i : ℝ) * Real.pi := by
      rw [← hi i]
      exact mul_pos hN (S.angle_pos i)
    exact_mod_cast (mul_pos_iff_of_pos_right Real.pi_pos).mp hp
  have hwb (i : Fin 3) : w i < D.natAbs := by
    have hh := mul_lt_mul_of_pos_left (S.angle_lt_pi i) hN
    rw [hi i] at hh
    exact_mod_cast (mul_lt_mul_iff_left₀ Real.pi_pos).mp hh
  have hang (i : Fin 3) : S.angle i = (w i : ℝ) * (Real.pi / D.natAbs) := by
    rw [← mul_div_assoc]
    apply (eq_div_iff hN.ne').mpr
    linear_combination hi i
  have hsum : ∑ i, w i = D.natAbs := by
    have hr : ((∑ i, w i : ℕ) : ℝ) = D.natAbs := by
      apply mul_right_cancel₀ Real.pi_ne_zero
      rw [Nat.cast_sum, Finset.sum_mul]
      simp_rw [← hi]
      rw [← Finset.mul_sum, Fin.sum_univ_three, S.angle_sum]
    exact_mod_cast hr
  have hN3 : 3 ≤ D.natAbs := by
    have hh := hsum
    rw [Fin.sum_univ_three] at hh
    have h0 := hwp 0
    have h1 := hwp 1
    have h2 := hwp 2
    omega
  exact ⟨hN3, w, hang, fun i => ⟨hwp i, hwb i⟩, hsum⟩

end Erdos633b.Triangle
