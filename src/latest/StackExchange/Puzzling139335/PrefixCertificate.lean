import StackExchange.Puzzling139335.PrefixCertificate.Algebra
import StackExchange.Puzzling139335.PrefixCertificate.AngularBounds

/-!
# The strict prefix support certificate

The five scalar inequalities arising from the strict prefix face in the
degree-(2,1,1,0) configuration are inconsistent.  This analytic theorem
has no geometric or topological hypotheses.  Its proof includes the
angular reductions, both half-angle polynomial identities, and the
strict rational positivity bounds.
-/

namespace Puzzling139335.PrefixCertificate

theorem support_angle_bound {a b l T : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : a + b < Real.pi / 2) (hl : 0 < l)
    (hT : T + l * Real.cos a ≤ 1 / 2)
    (hj : (1 - 2 * T) * Real.sin (a + b) ≤ l * (1 - Real.sin a)) :
    2 * Real.cos a * Real.sin (a + b) ≤ 1 - Real.sin a := by
  have hsin : 0 ≤ Real.sin (a + b) :=
    (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])).le
  have hjlow : 2 * l * Real.cos a ≤ 1 - 2 * T := by linarith
  have hmul := mul_le_mul_of_nonneg_right hjlow hsin
  by_contra h
  have hlt : 1 - Real.sin a < 2 * Real.cos a * Real.sin (a + b) := lt_of_not_ge h
  have hmul' := mul_lt_mul_of_pos_left hlt hl
  nlinarith

theorem trigD_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : a + b < Real.pi / 6) : 0 < trigD a b := by
  have hs : Real.sin b < 1 / 2 := by
    rw [← Real.sin_pi_div_six]
    exact Real.sin_lt_sin_of_lt_of_le_pi_div_two
      (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) (by linarith)
  have hc : (1 / 2 : ℝ) < Real.cos (a + b) := by
    rw [← Real.cos_pi_div_three]
    exact Real.cos_lt_cos_of_nonneg_of_le_pi
      (by linarith) (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  have hsa := Real.sin_le_one a
  unfold trigD
  linarith

theorem trigN_le_mul_trigD {a b l T : ℝ}
    (hj : (1 - 2 * T) * Real.sin (a + b) ≤ l * (1 - Real.sin a))
    (hfit : T * Real.sin (a + b) + (1 - l) * Real.cos (a + b) +
      l * Real.sin b ≤ 1) : trigN a b ≤ l * trigD a b := by
  unfold trigN trigD
  nlinarith

/-- The complete strict analytic certificate: the five support inequalities
cannot simultaneously hold for positive angles and positive side length. -/
theorem inconsistent {a b l T : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : a + b < Real.pi / 2) (hl : 0 < l)
    (hla : l ≤ Real.tan (a / 2))
    (hlb : l ≤ Real.tan (b / 2))
    (hT : T + l * Real.cos a ≤ 1 / 2)
    (hj : (1 - 2 * T) * Real.sin (a + b) ≤ l * (1 - Real.sin a))
    (hfit : T * Real.sin (a + b) + (1 - l) * Real.cos (a + b) +
      l * Real.sin b ≤ 1) : False := by
  have hH := support_angle_bound ha hb hab hl hT hj
  obtain ⟨hsmall, ht, hr, hsum, _hminpos, hmin⟩ := angular_bounds ha hb hab hH
  have hd : 0 < trigD a b := trigD_pos ha hb hsmall
  have hn : trigN a b ≤ l * trigD a b := trigN_le_mul_trigD hj hfit
  have hlmin : l ≤ min (Real.tan (a / 2)) (Real.tan (b / 2)) := le_min hla hlb
  have hnmin : trigN a b ≤
      min (Real.tan (a / 2)) (Real.tan (b / 2)) * trigD a b :=
    hn.trans (mul_le_mul_of_nonneg_right hlmin hd.le)
  have hca : Real.cos a ≠ -1 := by
    have hc : 0 < Real.cos a :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩
    linarith
  have hcb : Real.cos b ≠ -1 := by
    have hc : 0 < Real.cos b :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩
    linarith
  have hgap := rational_gap_min_pos ht hr hmin hsum
  rw [← trig_gap_eq_rational a b
    (min (Real.tan (a / 2)) (Real.tan (b / 2))) hca hcb] at hgap
  linarith

/-- The same certificate in the original support-angle coordinates. -/
theorem inconsistent_original_angles {θ φ l T : ℝ}
    (hφ : 0 < φ) (hφθ : φ < θ) (hθπ : θ < Real.pi / 2) (hl : 0 < l)
    (hla : l ≤ Real.cos θ / (1 + Real.sin θ))
    (hlb : l ≤ Real.tan (φ / 2))
    (hT : T + l * Real.sin θ ≤ 1 / 2)
    (hj : (1 - 2 * T) * Real.cos (θ - φ) ≤ l * (1 - Real.cos θ))
    (hfit : T * Real.cos (θ - φ) + (1 - l) * Real.sin (θ - φ) +
      l * Real.sin φ ≤ 1) : False := by
  have hθ : 0 < θ := hφ.trans hφθ
  have hsum : Real.pi / 2 - θ + φ = Real.pi / 2 - (θ - φ) := by ring
  apply inconsistent (a := Real.pi / 2 - θ) (b := φ) (l := l) (T := T)
    (by linarith) hφ (by linarith) hl
  · simpa only [tan_half_complement hθ hθπ] using hla
  · exact hlb
  · simpa only [Real.cos_pi_div_two_sub] using hT
  · simpa only [hsum, Real.sin_pi_div_two_sub] using hj
  · simpa only [hsum, Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub] using hfit

end Puzzling139335.PrefixCertificate
