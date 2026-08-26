import ErdosProblems.Erdos633.UTwoTiling

/-!
# Rational side criteria for the Y and U₂ families

The normalized rational tile has third side one. A single denominator
produces a positive integer cosine-law triple; the quadratic outer side
formulas therefore require dividing the scale by the denominator squared.
-/

namespace Erdos633

theorem oneTwenty_rational_integer_coordinates (a b : ℚ) (ha : 0 < a) (hb : 0 < b)
    (hconic : a ^ 2 + a * b + b ^ 2 = 1) :
    ∃ A B d : ℕ, 0 < A ∧ 0 < B ∧ 0 < d ∧ d ^ 2 = A ^ 2 + A * B + B ^ 2 ∧
      (A : ℝ) = (d : ℝ) * (a : ℝ) ∧ (B : ℝ) = (d : ℝ) * (b : ℝ) := by
  let r : Fin 2 → ℚ := ![a, b]
  have hr : ∀ i, 0 < r i := by intro i; fin_cases i <;> assumption
  obtain ⟨d, hd, k, hk, heq⟩ := positive_rationals_common_denominator r hr
  have hdQ : (d : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hd
  have hA : (k 0 : ℚ) = (d : ℚ) * a := by
    have h := (eq_div_iff hdQ).mp (heq 0)
    change a * d = k 0 at h
    rw [← h]; ring
  have hB : (k 1 : ℚ) = (d : ℚ) * b := by
    have h := (eq_div_iff hdQ).mp (heq 1)
    change b * d = k 1 at h
    rw [← h]; ring
  have hcQ : (d : ℚ) ^ 2 = (k 0 : ℚ) ^ 2 + (k 0 : ℚ) * k 1 + (k 1 : ℚ) ^ 2 := by
    rw [hA, hB]
    linear_combination -(d : ℚ) ^ 2 * hconic
  refine ⟨k 0, k 1, d, hk 0, hk 1, hd, by exact_mod_cast hcQ, ?_, ?_⟩
  · exact_mod_cast hA
  · exact_mod_cast hB

theorem Triangle.admitsNonsquareTiling_of_Y_rational_sides (P : Triangle)
    (a b : ℚ) (ha : 0 < a) (hb : 0 < b) (hconic : a ^ 2 + a * b + b ^ 2 = 1)
    (q : ℝ) (hq : 0 < q)
    (hab : dist P.a P.b = q * ((a : ℝ) + b))
    (hac : dist P.a P.c = q * (b : ℝ) * (2 * a + b))
    (hbc : dist P.b P.c = q * (a : ℝ)) : AdmitsNonsquareTiling P := by
  obtain ⟨A, B, d, hA, hB, hd, hc, hAR, hBR⟩ :=
    oneTwenty_rational_integer_coordinates a b ha hb hconic
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hd0 := ne_of_gt hdR
  apply P.admitsNonsquareTiling_of_Y_sides A B d hA hB hd hc
    (q / (d : ℝ) ^ 2) (div_pos hq (sq_pos_of_pos hdR))
  · rw [normSq_sub_eq_dist_sq, hab, hAR, hBR]
    field_simp
  · rw [normSq_sub_eq_dist_sq, hac, hAR, hBR]
    field_simp
  · rw [normSq_sub_eq_dist_sq, hbc, hAR]
    field_simp

theorem Triangle.admitsNonsquareTiling_of_U_two_rational_sides (P : Triangle)
    (a b : ℚ) (ha : 0 < a) (hb : 0 < b) (hconic : a ^ 2 + a * b + b ^ 2 = 1)
    (q : ℝ) (hq : 0 < q)
    (hab : dist P.a P.b = q * ((a : ℝ) + 2 * b))
    (hac : dist P.a P.c = q * (3 * (b : ℝ) * (a + b)))
    (hbc : dist P.b P.c = q) : AdmitsNonsquareTiling P := by
  obtain ⟨A, B, d, hA, hB, hd, hc, hAR, hBR⟩ :=
    oneTwenty_rational_integer_coordinates a b ha hb hconic
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hd0 := ne_of_gt hdR
  apply P.admitsNonsquareTiling_of_U_two_sides A B d hA hB hd hc
    (q / (d : ℝ) ^ 2) (div_pos hq (sq_pos_of_pos hdR))
  · rw [normSq_sub_eq_dist_sq, hab, hAR, hBR]
    field_simp
  · rw [normSq_sub_eq_dist_sq, hac, hAR, hBR]
    field_simp
  · rw [normSq_sub_eq_dist_sq, hbc]
    field_simp

end Erdos633
