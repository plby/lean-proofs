import ErdosProblems.Erdos633.EulerDescent

/-!
# The first parametrization in Euler's descent

Reduced rational coordinates are extracted from actual integer equations.
The square-root sign is selected before the numerator is reduced.
-/

namespace Erdos633

theorem square_root_avoiding_three (u z : ℤ) (hu3 : ¬ (3 : ℤ) ∣ u)
    (hz : IsSquare z) : ∃ w : ℤ, w ^ 2 = z ∧ ¬ (3 : ℤ) ∣ w - u := by
  obtain ⟨w, hw⟩ := hz
  by_cases hwu : (3 : ℤ) ∣ w - u
  · refine ⟨-w, by nlinarith only [hw], ?_⟩
    intro hneg
    have hsum := dvd_add hwu hneg
    have htwo : (3 : ℤ) ∣ 2 * u := by
      rw [show 2 * u = -((w - u) + (-w - u)) by ring]
      exact dvd_neg.mpr hsum
    have hp : Prime (3 : ℤ) := by norm_num
    rcases hp.dvd_mul.mp htwo with h | h
    · norm_num at h
    · exact hu3 h
  · exact ⟨w, by nlinarith only [hw], hwu⟩

theorem integer_ratio_coordinates (a b : ℤ) (hb : 0 < b) :
    ∃ m n : ℤ, 0 < n ∧ IsCoprime m n ∧ a * n = m * b ∧ m ∣ a ∧ n ∣ b := by
  let r : ℚ := (a : ℚ) / b
  have hc : IsCoprime r.num (r.den : ℤ) := by
    apply Int.isCoprime_iff_gcd_eq_one.mpr
    exact r.reduced
  have hn : (0 : ℤ) < r.den := by exact_mod_cast r.den_pos
  have heq : (a : ℚ) / b = (r.num : ℚ) / r.den := (Rat.num_div_den r).symm
  have hcrossQ := (div_eq_div_iff
    (by exact_mod_cast ne_of_gt hb : (b : ℚ) ≠ 0)
    (by exact_mod_cast r.den_ne_zero : (r.den : ℚ) ≠ 0)).mp heq
  have hcross : a * (r.den : ℤ) = r.num * b := by exact_mod_cast hcrossQ
  refine ⟨r.num, r.den, hn, hc, hcross, ?_, ?_⟩
  · exact hc.dvd_of_dvd_mul_right ⟨b, hcross⟩
  · exact hc.symm.dvd_of_dvd_mul_right ⟨a, by rw [mul_comm b, ← hcross]; ring⟩

theorem euler_first_parameters (ε u v : ℤ) (hε : ε ^ 2 = 1)
    (hu : 0 < u) (hv : 0 < v) (huv : IsCoprime u v)
    (hu3 : ¬ (3 : ℤ) ∣ u) (husq : IsSquare u)
    (hQ : IsSquare (eulerQuadratic ε u v)) :
    ∃ m n : ℤ, 0 < n ∧ IsCoprime m n ∧ ¬ (3 : ℤ) ∣ m ∧
      u = m ^ 2 - 3 * n ^ 2 ∧ v = n * (3 * ε * n - 2 * m) := by
  obtain ⟨w, hw, hwu⟩ := square_root_avoiding_three u (eulerQuadratic ε u v) hu3 hQ
  obtain ⟨m, n, hn, hmn, hcross, hmdvd, _⟩ := integer_ratio_coordinates (w - u) v hv
  have hm3 : ¬ (3 : ℤ) ∣ m := fun h => hwu (dvd_trans h hmdvd)
  have hparam : u * (n * (3 * ε * n - 2 * m)) = v * (m ^ 2 - 3 * n ^ 2) := by
    apply mul_left_cancel₀ (ne_of_gt hv)
    dsimp [eulerQuadratic] at hw
    linear_combination ((w + u) * n + m * v) * hcross - n ^ 2 * hw
  obtain ⟨hu', hv'⟩ := euler_parameter_fraction_eq ε u v m n hε hu huv husq hmn hm3 hparam
  exact ⟨m, n, hn, hmn, hm3, hu', hv'⟩

theorem euler_second_parameters (m n : ℤ) (hn : 0 < n)
    (hm3 : ¬ (3 : ℤ) ∣ m) (hsq : IsSquare (m ^ 2 - 3 * n ^ 2)) :
    ∃ U V : ℤ, 0 < V ∧ IsCoprime U V ∧ ¬ (3 : ℤ) ∣ U ∧
      2 * m * U * V = -n * (U ^ 2 + 3 * V ^ 2) := by
  obtain ⟨k, hk, hkm⟩ := square_root_avoiding_three m (m ^ 2 - 3 * n ^ 2) hm3 hsq
  obtain ⟨U, V, hV, hUV, hcross, hUdvd, _⟩ := integer_ratio_coordinates (k - m) n hn
  have hU3 : ¬ (3 : ℤ) ∣ U := fun h => hkm (dvd_trans h hUdvd)
  refine ⟨U, V, hV, hUV, hU3, ?_⟩
  apply mul_left_cancel₀ (ne_of_gt hn)
  linear_combination V ^ 2 * hk - ((k + m) * V + U * n) * hcross

end Erdos633
