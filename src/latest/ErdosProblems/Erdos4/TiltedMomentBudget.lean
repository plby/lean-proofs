import ErdosProblems.Erdos4.TiltedFiniteGcdMoments
import ErdosProblems.Erdos4.FGKMTInitialErrorBudget

/-! The finite gcd error is a negative logarithmic power under uniform size bounds. -/

namespace Erdos4.Tilted

open FGKMT Filter

theorem gcdTiltError_log_budget {L x τ D a : ℝ} {W R N : ℕ}
    (hL : 8 ≤ L) (hx : 1 ≤ x) (hW : L ^ 98 ≤ (W : ℝ))
    (hR : x ^ (1 / 4 : ℝ) ≤ (R : ℝ)) (hN : (N : ℝ) ^ τ ≤ x ^ (1 / 16 : ℝ))
    (hD0 : 0 ≤ D) (hD : D ≤ L ^ 5) (ha0 : 0 ≤ a) (ha : a ≤ L ^ 3)
    (hdom : 6 * L ^ 48 ≤ x ^ (1 / 16 : ℝ)) :
    gcdTiltError W R N τ D a ≤ 1 / L ^ 40 := by
  have hLpos : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hxpos : 0 < x := by linarith
  have hR1 : (1 : ℝ) ≤ R := (Real.one_le_rpow hx (by norm_num : (0 : ℝ) ≤ 1 / 4)).trans hR
  have hRpos : (0 : ℝ) < R := by linarith
  have hWtail : (W : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1 / L ^ 49 := by
    calc
      _ ≤ (L ^ (98 : ℕ)) ^ (-(1 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (pow_pos hLpos 98) hW (by norm_num)
      _ = _ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hLpos.le]
        norm_num [Real.rpow_neg hLpos.le]
  let z := 2 * a * (W : ℝ) ^ (-(1 / 2 : ℝ))
  have hz : z ≤ 2 / L ^ 46 := by
    calc
      _ ≤ 2 * L ^ 3 * (1 / L ^ 49) :=
        mul_le_mul (mul_le_mul_of_nonneg_left ha (by norm_num)) hWtail
          (Real.rpow_nonneg (Nat.cast_nonneg W) _) (by positivity)
      _ = _ := by field_simp
  have hε : 4 / L ^ 46 ≤ 1 := by
    apply (div_le_one (pow_pos hLpos 46)).mpr
    exact (show 4 ≤ L by linarith).trans (by
      simpa only [pow_one] using pow_le_pow_right₀ hL1 (by norm_num : 1 ≤ (46 : ℕ)))
  have he : Real.exp z - 1 ≤ 4 / L ^ 46 :=
    exp_sub_one_le_of_half_budget (by positivity) hε (hz.trans_eq (by ring))
  have he2 : Real.exp z ≤ 2 := by linarith
  have hfirst : D * (Real.exp z - 1) ≤ 4 / L ^ 41 := by
    calc
      _ ≤ D * (4 / L ^ 46) := mul_le_mul_of_nonneg_left he hD0
      _ ≤ L ^ 5 * (4 / L ^ 46) := mul_le_mul_of_nonneg_right hD (by positivity)
      _ = _ := by field_simp
  have hRtail : (R : ℝ) ^ (-(1 / 2 : ℝ)) ≤ x ^ (-(1 / 8 : ℝ)) := by
    calc
      _ ≤ (x ^ (1 / 4 : ℝ)) ^ (-(1 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hxpos _) hR (by norm_num)
      _ = _ := by rw [← Real.rpow_mul hxpos.le]; norm_num
  have hRinv : (R : ℝ)⁻¹ ≤ (R : ℝ) ^ (-(1 / 2 : ℝ)) := by
    have hh := Real.rpow_le_rpow_of_exponent_le hR1 (by norm_num : (-1 : ℝ) ≤ -(1 / 2 : ℝ))
    simpa only [Real.rpow_neg hRpos.le, Real.rpow_one] using hh
  have hL3 : 1 ≤ L ^ (3 : ℕ) := one_le_pow₀ hL1
  have htail : a / R + (R : ℝ) ^ (-(1 / 2 : ℝ)) * Real.exp z ≤
      3 * L ^ 3 * x ^ (-(1 / 8 : ℝ)) := by
    calc
      _ ≤ a * (R : ℝ) ^ (-(1 / 2 : ℝ)) + (R : ℝ) ^ (-(1 / 2 : ℝ)) * Real.exp z :=
        add_le_add (mul_le_mul_of_nonneg_left hRinv ha0) le_rfl
      _ = (a + Real.exp z) * (R : ℝ) ^ (-(1 / 2 : ℝ)) := by ring
      _ ≤ (L ^ 3 + 2) * x ^ (-(1 / 8 : ℝ)) :=
        mul_le_mul (add_le_add ha he2) hRtail (Real.rpow_nonneg (Nat.cast_nonneg R) _)
          (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hxpos.le _)
  have hsecond : (N : ℝ) ^ τ * (D * (a / R + (R : ℝ) ^ (-(1 / 2 : ℝ)) * Real.exp z)) ≤
      3 * L ^ 8 / x ^ (1 / 16 : ℝ) := by
    calc
      _ ≤ x ^ (1 / 16 : ℝ) * (L ^ 5 * (3 * L ^ 3 * x ^ (-(1 / 8 : ℝ)))) := by
        apply mul_le_mul hN _
          (mul_nonneg hD0 (add_nonneg (div_nonneg ha0 hRpos.le)
            (mul_nonneg (Real.rpow_nonneg hRpos.le _) (Real.exp_pos z).le)))
          (Real.rpow_nonneg hxpos.le _)
        exact mul_le_mul hD htail (by positivity) (pow_nonneg hLpos.le _)
      _ = 3 * L ^ 8 * (x ^ (1 / 16 : ℝ) * x ^ (-(1 / 8 : ℝ))) := by ring
      _ = _ := by
        rw [← Real.rpow_add hxpos]
        norm_num [Real.rpow_neg hxpos.le, div_eq_mul_inv]
  have hfirstSmall : 4 / L ^ 41 ≤ (1 / L ^ 40) / 2 := by
    have hh : 4 / L ≤ (1 : ℝ) / 2 := (div_le_iff₀ hLpos).mpr (by linarith)
    calc
      _ = (4 / L) * (1 / L ^ 40) := by field_simp
      _ ≤ (1 / 2) * (1 / L ^ 40) := mul_le_mul_of_nonneg_right hh (by positivity)
      _ = _ := by ring
  have hsecondSmall : 3 * L ^ 8 / x ^ (1 / 16 : ℝ) ≤ (1 / L ^ 40) / 2 := by
    calc
      _ ≤ 3 * L ^ 8 / (6 * L ^ 48) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hdom
      _ = _ := by field_simp; norm_num
  exact (add_le_add hfirst hsecond).trans (by linarith)

theorem eventually_gcdTiltError_budget :
    ∀ᶠ x : ℕ in atTop, ∀ W R N : ℕ, ∀ τ D a : ℝ,
      Real.log (x : ℝ) ^ (98 : ℕ) ≤ W →
      (x : ℝ) ^ (1 / 4 : ℝ) ≤ R → (N : ℝ) ^ τ ≤ (x : ℝ) ^ (1 / 16 : ℝ) →
      0 ≤ D → D ≤ Real.log (x : ℝ) ^ (5 : ℕ) →
      0 ≤ a → a ≤ Real.log (x : ℝ) ^ (3 : ℕ) →
      gcdTiltError W R N τ D a ≤ 1 / Real.log (x : ℝ) ^ (40 : ℕ) := by
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [hlog.eventually (eventually_ge_atTop 8), eventually_ge_atTop 1,
    eventually_const_log_power_le_rpow 48 6 (by norm_num : (0 : ℝ) < 1 / 16)]
    with x hL hx hdom
  intro W R N τ D a hW hR hN hD0 hD ha0 ha
  exact gcdTiltError_log_budget hL (by exact_mod_cast hx) hW hR hN hD0 hD ha0 ha hdom

end Erdos4.Tilted
