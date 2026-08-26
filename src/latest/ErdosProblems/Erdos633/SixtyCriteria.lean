import ErdosProblems.Erdos633.WTiling

/-!
# The 60-degree sufficient condition

The W construction and doubled-leg descent apply to every triangle with a
60-degree angle and commensurable sides, including all positions and scales.
The equal adjacent-side case is handled by the actual isosceles construction.
-/

namespace Erdos633

theorem Triangle.sixty_integer_cosine_relation (P : Triangle)
    (hangle : P.angleA = Real.pi / 3) (u v w : ℕ)
    (q : ℝ) (hq : 0 < q)
    (hab : dist P.a P.b = q * u) (hac : dist P.a P.c = q * v)
    (hbc : dist P.b P.c = q * w) :
    w ^ 2 + u * v = u ^ 2 + v ^ 2 := by
  have hcos := EuclideanGeometry.law_cos P.b P.a P.c
  rw [dist_comm P.b P.a, dist_comm P.c P.a, hab, hac, hbc] at hcos
  change (q * w) * (q * w) = (q * u) * (q * u) + (q * v) * (q * v) -
    2 * (q * u) * (q * v) * Real.cos P.angleA at hcos
  rw [hangle, Real.cos_pi_div_three] at hcos
  have heq : (w : ℝ) ^ 2 + (u : ℝ) * v = (u : ℝ) ^ 2 + (v : ℝ) ^ 2 := by
    apply mul_left_cancel₀ (pow_ne_zero 2 (ne_of_gt hq))
    nlinarith only [hcos]
  exact_mod_cast heq

theorem Triangle.admitsNonsquareTiling_of_sixty_ordered_integer_sides
    (P : Triangle) (u v w : ℕ) (hu : 0 < u) (huv : u < v) (hw : 0 < w)
    (hconic : w ^ 2 + u * v = u ^ 2 + v ^ 2)
    (q : ℝ) (hq : 0 < q)
    (hab : dist P.a P.b = q * u) (hac : dist P.a P.c = q * v)
    (hbc : dist P.b P.c = q * w) : AdmitsNonsquareTiling P := by
  have hdiff : u + (v - u) = v := by omega
  have hdiffR : (u : ℝ) + (v - u : ℕ) = v := by exact_mod_cast hdiff
  have heq : w ^ 2 = u ^ 2 + u * (v - u) + (v - u) ^ 2 := by
    nlinarith only [hconic, hdiff]
  apply P.admitsNonsquareTiling_of_W_integer_sides u (v - u) w hu
    (by omega) hw heq q hq
  · rw [normSq_sub_eq_dist_sq, hab]
    ring
  · rw [normSq_sub_eq_dist_sq, hac, hdiffR]
    ring
  · rw [normSq_sub_eq_dist_sq, hbc]
    ring

/-- A 60-degree angle and positive integer side ratios suffice, without a
separate Diophantine or nonsquareness hypothesis. -/
theorem Triangle.admitsNonsquareTiling_of_sixty_integer_sides (P : Triangle)
    (hangle : P.angleA = Real.pi / 3) (u v w : ℕ)
    (hu : 0 < u) (hv : 0 < v) (hw : 0 < w) (q : ℝ) (hq : 0 < q)
    (hab : dist P.a P.b = q * u) (hac : dist P.a P.c = q * v)
    (hbc : dist P.b P.c = q * w) : AdmitsNonsquareTiling P := by
  have heq := P.sixty_integer_cosine_relation hangle u v w q hq hab hac hbc
  rcases lt_trichotomy u v with huv | huv | huv
  · exact P.admitsNonsquareTiling_of_sixty_ordered_integer_sides u v w hu huv hw
      heq q hq hab hac hbc
  · apply P.admitsNonsquareTiling_of_isosceles
    exact Or.inl (by rw [hab, hac, huv])
  · have hT := P.swapBC.admitsNonsquareTiling_of_sixty_ordered_integer_sides
      v u w hv huv hw (by nlinarith only [heq]) q hq hac hab
      (by simpa only [Triangle.swapBC, dist_comm] using hbc)
    exact admitsNonsquareTiling_of_carrier_eq hT P.swapBC_carrier

/-- Rational side coordinates are cleared simultaneously, preserving the
actual triangle and obtaining the integer criterion above. -/
theorem Triangle.admitsNonsquareTiling_of_sixty_rational_sides (P : Triangle)
    (hangle : P.angleA = Real.pi / 3) (a b c : ℚ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (q : ℝ) (hq : 0 < q)
    (hab : dist P.a P.b = q * a) (hac : dist P.a P.c = q * b)
    (hbc : dist P.b P.c = q * c) : AdmitsNonsquareTiling P := by
  let r : Fin 3 → ℚ := ![a, b, c]
  have hr : ∀ i, 0 < r i := by
    intro i
    fin_cases i <;> assumption
  obtain ⟨d, hd, k, hk, heq⟩ := positive_rationals_common_denominator r hr
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have heqR (i : Fin 3) : ((r i : ℚ) : ℝ) = (k i : ℝ) / d := by
    simpa only [Rat.cast_div, Rat.cast_natCast] using
      congrArg (fun x : ℚ => (x : ℝ)) (heq i)
  apply P.admitsNonsquareTiling_of_sixty_integer_sides hangle (k 0) (k 1) (k 2)
    (hk 0) (hk 1) (hk 2) (q / d) (div_pos hq hdR)
  · rw [hab, show (a : ℝ) = (k 0 : ℝ) / d from heqR 0]
    ring
  · rw [hac, show (b : ℝ) = (k 1 : ℝ) / d from heqR 1]
    ring
  · rw [hbc, show (c : ℝ) = (k 2 : ℝ) / d from heqR 2]
    ring

end Erdos633
