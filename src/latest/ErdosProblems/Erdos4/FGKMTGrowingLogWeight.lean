import ErdosProblems.Erdos4.FGKMTLogarithmicAbsorption

/-! Absorption uniform in a logarithmically growing divisor multiplicity. -/

namespace Erdos4.FGKMT

open Filter Asymptotics

theorem eventually_growing_log_weight {a : ℝ} (ha : 0 < a) :
    ∀ᶠ x : ℕ in atTop, ∀ d Q : ℕ, Q ≤ x →
      (d : ℝ) ≤ Real.log (x : ℝ) ^ (1 / 8 : ℝ) →
      (1 + Real.log (Q : ℝ)) ^ (2 * d ^ 2) ≤
        Real.exp ((a / 4) * Real.sqrt (Real.log (x : ℝ))) := by
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hsmall := ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp_tendsto
    hlog).bound (show 0 < a / 16 by positivity)
  filter_upwards [hsmall, hlog.eventually (eventually_ge_atTop 2), eventually_ge_atTop 1]
    with x hsmall hlarge hx
  change 2 ≤ Real.log (x : ℝ) at hlarge
  have hLpos : 0 < Real.log (x : ℝ) := by linarith
  have hlogL : 0 ≤ Real.log (Real.log (x : ℝ)) := Real.log_nonneg (by linarith)
  have hsmall' : Real.log (Real.log (x : ℝ)) ≤
      (a / 16) * Real.log (x : ℝ) ^ (1 / 4 : ℝ) := by
    simpa only [Function.comp_apply, Real.norm_eq_abs, abs_of_nonneg hlogL,
      abs_of_nonneg (Real.rpow_nonneg hLpos.le (1 / 4 : ℝ))] using hsmall
  intro d Q hQx hd
  have hlogQ : Real.log (Q : ℝ) ≤ Real.log (x : ℝ) := by
    by_cases hQ : Q = 0
    · simpa [hQ] using hLpos.le
    · exact Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hQ) (by exact_mod_cast hQx)
  have hbase : 0 < 1 + Real.log (Q : ℝ) := by
    have hh := Real.log_natCast_nonneg Q
    positivity
  have hlogBase : Real.log (1 + Real.log (Q : ℝ)) ≤ 2 * Real.log (Real.log (x : ℝ)) := by
    calc
      _ ≤ Real.log (Real.log (x : ℝ) ^ 2) := by
        apply Real.log_le_log hbase
        nlinarith
      _ = _ := by rw [Real.log_pow]; norm_num
  have hpow2 : (Real.log (x : ℝ) ^ (1 / 8 : ℝ)) ^ 2 =
      Real.log (x : ℝ) ^ (1 / 4 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hLpos.le]
    norm_num
  have hd2 : (d : ℝ) ^ 2 ≤ Real.log (x : ℝ) ^ (1 / 4 : ℝ) :=
    (pow_le_pow_left₀ (Nat.cast_nonneg d) hd 2).trans_eq hpow2
  have hquarter : Real.log (x : ℝ) ^ (1 / 4 : ℝ) * Real.log (x : ℝ) ^ (1 / 4 : ℝ) =
      Real.sqrt (Real.log (x : ℝ)) := by
    rw [← Real.rpow_add hLpos]
    norm_num
    exact (Real.sqrt_eq_rpow _).symm
  have hexponent : ((2 * d ^ 2 : ℕ) : ℝ) * Real.log (1 + Real.log (Q : ℝ)) ≤
      (a / 4) * Real.sqrt (Real.log (x : ℝ)) := by
    push_cast
    calc
      _ ≤ (2 * (d : ℝ) ^ 2) * (2 * Real.log (Real.log (x : ℝ))) :=
        mul_le_mul_of_nonneg_left hlogBase (by positivity)
      _ ≤ (2 * Real.log (x : ℝ) ^ (1 / 4 : ℝ)) * (2 * Real.log (Real.log (x : ℝ))) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hd2 (by norm_num)) (by positivity)
      _ ≤ (2 * Real.log (x : ℝ) ^ (1 / 4 : ℝ)) *
          (2 * ((a / 16) * Real.log (x : ℝ) ^ (1 / 4 : ℝ))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsmall' (by norm_num)) (by positivity)
      _ = (a / 4) * (Real.log (x : ℝ) ^ (1 / 4 : ℝ) * Real.log (x : ℝ) ^ (1 / 4 : ℝ)) := by ring
      _ = _ := by rw [hquarter]
  calc
    _ = Real.exp (((2 * d ^ 2 : ℕ) : ℝ) * Real.log (1 + Real.log (Q : ℝ))) := by
      rw [← Real.log_pow, Real.exp_log (pow_pos hbase _)]
    _ ≤ _ := Real.exp_le_exp.mpr hexponent

end Erdos4.FGKMT
