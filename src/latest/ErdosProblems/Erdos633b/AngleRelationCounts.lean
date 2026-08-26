import ErdosProblems.Erdos633b.AngleCoefficientIndependence

/-! Integer separation for any two-angle relation, independent of the
corner-column labels. This is used for the local vertex-type tables. -/

namespace Erdos633b.Triangle

theorem irrational_first_of_angle_relation (S : Triangle) (P Q : ℕ) (hQ : Q ≠ 0)
    (hrel : (P : ℝ) * S.angle 0 + (Q : ℝ) * S.angle 1 = Real.pi)
    (hirr : ¬ ∀ i, IsRational (S.angle i / Real.pi)) :
    Irrational (S.angle 0 / Real.pi) := by
  have hQ0 : (Q : ℝ) ≠ 0 := by exact_mod_cast hQ
  rintro ⟨a, ha⟩
  have haa : (a : ℝ) * Real.pi = S.angle 0 := (eq_div_iff Real.pi_ne_zero).mp ha
  let b : ℚ := (1 - P * a) / Q
  have hb : (b : ℝ) = S.angle 1 / Real.pi := by
    dsimp [b]
    push_cast
    apply (div_eq_div_iff hQ0 Real.pi_ne_zero).mpr
    linear_combination -hrel - (P : ℝ) * haa
  have hc : IsRational (S.angle 2 / Real.pi) := by
    refine ⟨1 - a - b, ?_⟩
    push_cast
    rw [ha, hb]
    apply (eq_div_iff Real.pi_ne_zero).mpr
    field_simp
    linarith [S.angle_sum]
  apply hirr
  intro i
  fin_cases i
  · exact ⟨a, ha⟩
  · exact ⟨b, hb⟩
  · exact hc

theorem local_angle_integer_equations (S : Triangle) (P Q : ℕ) (hQ : Q ≠ 0)
    (hrel : (P : ℝ) * S.angle 0 + (Q : ℝ) * S.angle 1 = Real.pi)
    (hirr : Irrational (S.angle 0 / Real.pi)) (p q r k : ℕ)
    (hs : (p : ℝ) * S.angle 0 + (q : ℝ) * S.angle 1 +
      (r : ℝ) * S.angle 2 = k * Real.pi) :
    p + P * r = P * k + r ∧ q + Q * r = Q * k + r := by
  let u : ℤ := p + (P : ℤ) * r - (P : ℤ) * k - r
  let v : ℤ := q + (Q : ℤ) * r - (Q : ℤ) * k - r
  have he : (u : ℝ) * S.angle 0 + (v : ℝ) * S.angle 1 = 0 := by
    dsimp [u, v]
    push_cast
    linear_combination hs - (r : ℝ) * S.angle_sum + ((r : ℝ) - k) * hrel
  obtain ⟨hu, hv⟩ := two_angle_integer_coefficients P Q (by exact_mod_cast hQ)
    (by simpa only [Int.cast_natCast] using hrel) hirr u v he
  dsimp [u, v] at hu hv
  have hu' : (p : ℤ) + (P : ℤ) * r = (P : ℤ) * k + r := by omega
  have hv' : (q : ℤ) + (Q : ℤ) * r = (Q : ℤ) * k + r := by omega
  exact ⟨by exact_mod_cast hu', by exact_mod_cast hv'⟩

end Erdos633b.Triangle
