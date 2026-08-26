import ErdosProblems.Erdos67b.MRSmallPrimeSaving

/-!
# Uniform product scales for the small-prime exceptional budget

One explicit logarithmic threshold pays all scalar conditions. The final
block is chosen before the time range, additional prime interval, or
small-value threshold.
-/

namespace Erdos67b

noncomputable section

def mrExceptionalLogScaleThreshold (eta q₁ : ℝ) : ℝ :=
  1 + q₁ ^ 2 + 8 * mrNoSmallCountConstant / eta + (56 / eta) ^ 2 +
    8 / eta + Real.exp (8 / eta)

theorem mrExceptionalLogScaleThreshold_spec
    {eta q₁ R : ℝ} (heta : 0 < eta) (hq : 1 ≤ q₁)
    (hR : mrExceptionalLogScaleThreshold eta q₁ ≤ R) :
    1 ≤ R ∧ q₁ ≤ Real.sqrt R ∧ 8 * mrNoSmallCountConstant / eta ≤ R ∧
      (56 / eta) ^ 2 ≤ R ∧ 8 / eta ≤ R ∧ 8 / eta ≤ Real.log R := by
  have hC : 0 ≤ 8 * mrNoSmallCountConstant / eta := by
    exact div_nonneg (mul_nonneg (by norm_num) mrNoSmallCountConstant_pos.le) heta.le
  have hf : 0 ≤ 8 / eta := by positivity
  have he : 0 < Real.exp (8 / eta) := Real.exp_pos _
  unfold mrExceptionalLogScaleThreshold at hR
  have hR1 : 1 ≤ R := by nlinarith [sq_nonneg q₁, sq_nonneg (56 / eta)]
  have hqR : q₁ ^ 2 ≤ R := by nlinarith [sq_nonneg (56 / eta)]
  have hs : q₁ ≤ Real.sqrt R := by
    nlinarith [Real.sq_sqrt (show 0 ≤ R by linarith), Real.sqrt_nonneg R]
  have hexp : Real.exp (8 / eta) ≤ R := by nlinarith [sq_nonneg q₁, sq_nonneg (56 / eta)]
  have hlog := Real.log_le_log he hexp
  rw [Real.log_exp] at hlog
  refine ⟨hR1, hs, ?_, ?_, ?_, hlog⟩ <;> nlinarith [sq_nonneg q₁, sq_nonneg (56 / eta)]

theorem mrExists_lastBlock_smallPrime_budgets
    {eta p₁ q₁ : ℝ} (heta0 : 0 < eta) (heta1 : eta ≤ 1 / 12)
    (hp : 2 ≤ p₁) (hq : 1 ≤ q₁) (hpq : p₁ ≤ q₁)
    (hlogq : 1 ≤ Real.log q₁) (hbudget : 4096 * Real.log q₁ ≤ eta * p₁)
    {X : ℕ} (hX : 0 < X) {R : ℝ} (hR : R = Real.log (X : ℝ))
    (hscale : mrExceptionalLogScaleThreshold eta q₁ ≤ R) :
    ∃ J : ℕ, 1 ≤ J ∧ mrLogScheduleUpper q₁ J ≤ Real.sqrt R ∧
      Real.sqrt R < mrLogScheduleUpper q₁ (J + 1) ∧
      ∀ (U : ℕ) (T V : ℝ), 1 ≤ T → T ≤ X →
        (U : ℝ) ≤ Real.exp (R / Real.log R + 1) →
        mrExceptionalSmallPrimeEnergyBudget eta p₁ q₁ J U X T V ≤
          2 * mrSmallPrimeLogConstant * V ^ 2 * R ^ 2 := by
  obtain ⟨hR1, hqR, hconstant, hsqrt, hRlarge, hlogR⟩ :=
    mrExceptionalLogScaleThreshold_spec heta0 hq hscale
  obtain ⟨J, hJ, hJR, hnext⟩ := mrLogSchedule_exists_last_block hq hqR
  refine ⟨J, hJ, hJR, hnext, ?_⟩
  intro U T V hT hTX hU
  have haux : (U : ℝ) ≤ Real.exp (eta * R / 4) :=
    hU.trans (Real.exp_le_exp.mpr (mrAuxiliary_log_upper_le_small_power heta0 hRlarge hlogR))
  exact mrExceptionalSmallPrimeEnergyBudget_le_log_sq heta0 heta1 hp hq hpq hlogq hbudget
    hJ hX hR hR1 hT hTX hJR hnext.le hconstant hsqrt haux

/-- A single natural threshold works for every later product scale, with
the final block chosen independently of the sampled polynomial. -/
theorem mrExists_smallPrime_product_scale
    {eta p₁ q₁ : ℝ} (heta0 : 0 < eta) (heta1 : eta ≤ 1 / 12)
    (hp : 2 ≤ p₁) (hq : 1 ≤ q₁) (hpq : p₁ ≤ q₁)
    (hlogq : 1 ≤ Real.log q₁) (hbudget : 4096 * Real.log q₁ ≤ eta * p₁) :
    ∃ X₀ : ℕ, 0 < X₀ ∧ ∀ X : ℕ, X₀ ≤ X →
      ∃ J : ℕ, 1 ≤ J ∧ mrLogScheduleUpper q₁ J ≤ Real.sqrt (Real.log (X : ℝ)) ∧
        Real.sqrt (Real.log (X : ℝ)) < mrLogScheduleUpper q₁ (J + 1) ∧
        ∀ (U : ℕ) (T V : ℝ), 1 ≤ T → T ≤ X →
          (U : ℝ) ≤ Real.exp (Real.log (X : ℝ) / Real.log (Real.log (X : ℝ)) + 1) →
          mrExceptionalSmallPrimeEnergyBudget eta p₁ q₁ J U X T V ≤
            2 * mrSmallPrimeLogConstant * V ^ 2 * Real.log (X : ℝ) ^ 2 := by
  let R₀ := mrExceptionalLogScaleThreshold eta q₁
  let X₀ : ℕ := ⌈Real.exp R₀⌉₊
  have hX₀ : 0 < X₀ := Nat.ceil_pos.mpr (Real.exp_pos _)
  refine ⟨X₀, hX₀, ?_⟩
  intro X hX₀X
  have hX : 0 < X := hX₀.trans_le hX₀X
  have hexp : Real.exp R₀ ≤ (X : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hX₀X)
  have hscale : R₀ ≤ Real.log (X : ℝ) := by
    have hh := Real.log_le_log (Real.exp_pos R₀) hexp
    simpa only [Real.log_exp] using hh
  exact mrExists_lastBlock_smallPrime_budgets heta0 heta1 hp hq hpq hlogq hbudget hX rfl hscale

end

end Erdos67b
