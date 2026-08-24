import ErdosProblems.Erdos587.CriticalSquare
import ErdosProblems.Erdos587.PrimitiveParameters

/-! The critical primitive terminal branch at fixed logarithmic loss. -/

open Filter

namespace Erdos587

theorem exists_critical_primitive_terminal (C : ℝ) (hC : 0 < C) :
    ∃ B : ℕ, 0 < B ∧ ∃ T₀ : ℝ, ∀ (t u v H J T : ℕ), T₀ ≤ (T : ℝ) →
      0 < u → 0 < v → 0 < H → H ≤ v → u.Coprime v →
      t + u * H + v * J ≤ T → u * H ≤ v * J →
      (T : ℝ) ≤ C * ((u * H + v * J : ℕ) : ℝ) →
      (T : ℝ) ^ (1 / 16 : ℝ) ≤ u →
      (J : ℝ) ≤ (T : ℝ) ^ (1 / 4 + 1 / 1000 : ℝ) →
      (T : ℝ) ^ (1 / 4 : ℝ) * (1 + Real.log T) ^ B ≤ J →
      (T : ℝ) ^ (3 / 4 : ℝ) * (1 + Real.log T) ^ B ≤ (H : ℝ) * J →
      ∃ x ≤ H, ∃ y ≤ J, ∃ z : ℕ, 0 < z ∧ z ^ 2 = t + u * x + v * y := by
  let c₀ : ℝ := 1 / (2 * C)
  have hc₀ : 0 < c₀ := by dsimp [c₀]; positivity
  obtain ⟨A, hA, K, hK, O, hO, hcritical⟩ := exists_critical_square_of_main_budgets C c₀ hC hc₀
  have hconditions := hcritical.and ((eventually_ge_atTop (1 : ℝ)).and
    (Real.tendsto_log_atTop.eventually_ge_atTop (max A K)))
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp hconditions
  refine ⟨O + 1, by omega, T₀, ?_⟩
  intro t u v H J T hbig hu hv hH hHv huv hambient horient hspan hu0 hJhi hside hprod
  obtain ⟨hcrit, hT1, hlog⟩ := hT₀ (T : ℝ) hbig
  have hT : (0 : ℝ) < T := by linarith
  let Λ : ℝ := 1 + Real.log (T : ℝ)
  have hΛ1 : 1 ≤ Λ := by
    dsimp [Λ]
    have := Real.log_nonneg hT1
    linarith
  have hΛpos : 0 < Λ := by linarith
  have hΛA : A ≤ Λ := by
    dsimp [Λ]
    have := le_max_left A K
    linarith
  have hΛK : K < Λ := by
    dsimp [Λ]
    have := le_max_right A K
    linarith
  have hpow1 : 1 ≤ Λ ^ (O + 1) := one_le_pow₀ hΛ1
  have hJlo : (T : ℝ) ^ (1 / 4 : ℝ) ≤ J :=
    (le_mul_of_one_le_right (Real.rpow_nonneg hT.le _) hpow1).trans hside
  have hprod0 : (T : ℝ) ^ (3 / 4 : ℝ) ≤ (H : ℝ) * J :=
    (le_mul_of_one_le_right (Real.rpow_nonneg hT.le _) hpow1).trans hprod
  have hambientR : (t : ℝ) + u * H + v * J ≤ T := by exact_mod_cast hambient
  have horientR : (u : ℝ) * H ≤ v * J := by exact_mod_cast horient
  have hspanR : (T : ℝ) ≤ C * ((u : ℝ) * H + v * J) := by
    simpa only [Nat.cast_add, Nat.cast_mul] using hspan
  obtain ⟨hHlo, huhi, hvlo, hvhi⟩ := critical_parameter_ranges
    (Nat.cast_nonneg t) (Nat.cast_nonneg u) (Nat.cast_nonneg v)
    (Nat.cast_nonneg H) (Nat.cast_nonneg J) hT hC hambientR horientR hspanR hJlo hJhi hprod0
  have huH : (u : ℝ) * H ≤ T := by
    have ht0 := Nat.cast_nonneg (α := ℝ) t
    have hvJ0 : (0 : ℝ) ≤ v * J := by positivity
    linarith
  have hdensity := primitive_width_density_budget (Nat.cast_nonneg u) (Nat.cast_nonneg J)
    (show (0 : ℝ) < H by exact_mod_cast hH) hT hΛpos.le huH hside
    (show (T : ℝ) ^ (3 / 4 : ℝ) * Λ ^ (O + 1) ≤ (J : ℝ) * H by
      simpa only [mul_comm] using hprod)
  have hΛpow : Λ ≤ Λ ^ (O + 1) := by
    rw [pow_succ]
    exact le_mul_of_one_le_left hΛpos.le (one_le_pow₀ hΛ1)
  have hJden : A * Real.sqrt (u : ℝ) ≤ J := by
    calc
      _ ≤ Λ ^ (O + 1) * Real.sqrt (u : ℝ) :=
        mul_le_mul_of_nonneg_right (hΛA.trans hΛpow) (Real.sqrt_nonneg _)
      _ = Real.sqrt (u : ℝ) * Λ ^ (O + 1) := mul_comm _ _
      _ ≤ J := hdensity
  have hprodstrong : K * (T : ℝ) ^ (3 / 4 : ℝ) * Λ ^ O < (H : ℝ) * J := by
    calc
      _ = (T : ℝ) ^ (3 / 4 : ℝ) * Λ ^ O * K := by ring
      _ < (T : ℝ) ^ (3 / 4 : ℝ) * Λ ^ O * Λ :=
        mul_lt_mul_of_pos_left hΛK (by positivity)
      _ = (T : ℝ) ^ (3 / 4 : ℝ) * Λ ^ (O + 1) := by rw [pow_succ]; ring
      _ ≤ (H : ℝ) * J := hprod
  obtain ⟨a, b, hab, hb⟩ := exists_nat_positive_bezout hu hv huv
  exact hcrit a b t u v H J hu hv hH hHv hab hb huv hambientR horientR hspanR
    hu0 huhi hvlo hvhi hHlo hJden hprodstrong

end Erdos587
