import ErdosProblems.Erdos587.HooleyWideSquare
import ErdosProblems.Erdos587.PrimitiveParameters

/-! # The power-separated primitive terminal branch at the tenth log-log power -/

open Filter

namespace Erdos587

theorem exists_delta_wide_primitive_terminal (C : ℝ) (hC : 0 < C) :
    ∃ T₀ : ℝ, ∀ t u v H J T : ℕ, T₀ ≤ (T : ℝ) →
      0 < u → 0 < v → 0 < H → 0 < J → H ≤ v → u.Coprime v →
      t + u * H + v * J ≤ T → u * H ≤ v * J →
      (T : ℝ) ≤ C * ((u * H + v * J : ℕ) : ℝ) →
      (T : ℝ) ^ (1 / 4 : ℝ) * (max 1 (Real.log (Real.log (T : ℝ)))) ^ 10 ≤ H →
      (T : ℝ) ^ (3 / 4 : ℝ) * (max 1 (Real.log (Real.log (T : ℝ)))) ^ 10 ≤ (H : ℝ) * J →
      (T : ℝ) ^ (1 / 4 + 1 / 1000 : ℝ) ≤ J →
      ∃ x ≤ H, ∃ y ≤ J, ∃ z : ℕ, 0 < z ∧ z ^ 2 = t + u * x + v * y := by
  obtain ⟨A, hA, hwide⟩ := exists_delta_wide_square_of_main_budgets C hC
  have hconditions := hwide.and ((eventually_ge_atTop (1 : ℝ)).and
    ((Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop (max 8 A)))
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp hconditions
  refine ⟨T₀, ?_⟩
  intro t u v H J T hbig hu hv hH hJ hHv huv hambient horient hspan hside hprod hJlarge
  obtain ⟨hwideT, hT1, hlog⟩ := hT₀ (T : ℝ) hbig
  change max 8 A ≤ Real.log (Real.log (T : ℝ)) at hlog
  have hT : (0 : ℝ) < T := by linarith
  let Λ := max 1 (Real.log (Real.log (T : ℝ)))
  have hΛ1 : 1 ≤ Λ := le_max_left _ _
  have hΛpos : 0 < Λ := zero_lt_one.trans_le hΛ1
  have hlogΛ : Real.log (Real.log (T : ℝ)) ≤ Λ := le_max_right _ _
  have hΛ8 : 8 ≤ Λ := (le_max_left 8 A).trans (hlog.trans hlogΛ)
  have hΛA : A ≤ Λ := (le_max_right 8 A).trans (hlog.trans hlogΛ)
  have hΛpow : Λ ≤ Λ ^ 10 := by
    simpa only [pow_one] using pow_le_pow_right₀ hΛ1 (show 1 ≤ 10 by omega)
  have hvJ : (v : ℝ) * J ≤ T := by exact_mod_cast (show v * J ≤ T by omega)
  have hJR : (0 : ℝ) < J := by exact_mod_cast hJ
  have hdensity := primitive_width_density_budget (Nat.cast_nonneg v) (Nat.cast_nonneg H)
    hJR hT hΛpos.le hvJ hside hprod
  have hHden : A * Real.sqrt (v : ℝ) ≤ H := by
    calc
      _ ≤ Λ ^ 10 * Real.sqrt (v : ℝ) :=
        mul_le_mul_of_nonneg_right (hΛA.trans hΛpow) (Real.sqrt_nonneg _)
      _ = Real.sqrt (v : ℝ) * Λ ^ 10 := mul_comm _ _
      _ ≤ H := hdensity
  have hcutoff := primitive_width_cutoff_budget (B := 9) (Nat.cast_nonneg v) (Nat.cast_nonneg H)
    hJR hT hΛ8 hvJ hprod
  have hbudget : (v : ℝ) * Λ ^ 7 ≤ H * (T : ℝ) ^ (1 / 4 : ℝ) := by
    calc
      _ ≤ (v : ℝ) * Λ ^ 9 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hΛ1 (by omega)) (Nat.cast_nonneg v)
      _ ≤ ((H : ℝ) / 8) * (T : ℝ) ^ (1 / 4 : ℝ) := hcutoff
      _ ≤ _ := mul_le_mul_of_nonneg_right (div_le_self (Nat.cast_nonneg H) (by norm_num))
        (Real.rpow_nonneg hT.le _)
  have hvhi := modulus_upper_of_large_second_side (Nat.cast_nonneg v) hT hvJ hJlarge
  have hambientR : (t : ℝ) + u * H + v * J ≤ T := by exact_mod_cast hambient
  have horientR : (u : ℝ) * H ≤ v * J := by exact_mod_cast horient
  have hspanR : (T : ℝ) ≤ C * ((u : ℝ) * H + v * J) := by
    simpa only [Nat.cast_add, Nat.cast_mul] using hspan
  obtain ⟨a, b, hab, _hb⟩ := exists_nat_positive_bezout hu hv huv
  exact hwideT a b t u v H J hv hH hHv hab huv hambientR horientR hspanR hvhi hHden hbudget

end Erdos587
