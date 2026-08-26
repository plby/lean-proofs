import ErdosProblems.Erdos67b.MRExceptionalCountBounds

/-!
# Last block for the exceptional sample count

The first schedule crossing of `sqrt R` supplies a positive final block.
The next block pays the moment cost, and the current block controls the
remaining factor uniformly in `R`.
-/

namespace Erdos67b

noncomputable section

theorem mrLogScheduleUpper_sq_index_le {q₁ : ℝ} (hq : 1 ≤ q₁)
    {j : ℕ} (hj : 1 ≤ j) : (j : ℝ) ^ 2 ≤ mrLogScheduleUpper q₁ j := by
  have hjr : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hp : (j : ℝ) ^ 2 ≤ (j : ℝ) ^ (4 * j + 2) :=
    pow_le_pow_right₀ hjr (by omega)
  have hqpow := one_le_pow₀ (n := j) hq
  unfold mrLogScheduleUpper
  have hpos : 0 ≤ (j : ℝ) ^ (4 * j + 2) := by positivity
  nlinarith

theorem mrLogSchedule_exists_last_block {q₁ R : ℝ} (hq : 1 ≤ q₁)
    (hqR : q₁ ≤ Real.sqrt R) :
    ∃ J : ℕ, 1 ≤ J ∧ mrLogScheduleUpper q₁ J ≤ Real.sqrt R ∧
      Real.sqrt R < mrLogScheduleUpper q₁ (J + 1) := by
  classical
  have hex : ∃ n : ℕ, Real.sqrt R < mrLogScheduleUpper q₁ (n + 1) := by
    refine ⟨⌈Real.sqrt R⌉₊, ?_⟩
    have hc := Nat.le_ceil (Real.sqrt R)
    have hs := mrLogScheduleUpper_sq_index_le hq (j := ⌈Real.sqrt R⌉₊ + 1) (by omega)
    have hj : (1 : ℝ) ≤ (⌈Real.sqrt R⌉₊ + 1 : ℕ) := by exact_mod_cast (by omega : 1 ≤ ⌈Real.sqrt R⌉₊ + 1)
    push_cast at hs hj ⊢
    nlinarith
  let J := Nat.find hex
  have hnext : Real.sqrt R < mrLogScheduleUpper q₁ (J + 1) := Nat.find_spec hex
  have hJ : 1 ≤ J := by
    by_contra h
    have hzero : J = 0 := by omega
    simp only [hzero, zero_add, mrLogScheduleUpper, Nat.cast_one, one_pow, one_mul, pow_one] at hnext
    linarith
  have hprev : mrLogScheduleUpper q₁ J ≤ Real.sqrt R := by
    by_contra h
    have hh : Real.sqrt R < mrLogScheduleUpper q₁ (J - 1 + 1) := by
      simpa only [Nat.sub_add_cancel hJ] using lt_of_not_ge h
    have hmin : J ≤ J - 1 := Nat.find_min' hex hh
    omega
  exact ⟨J, hJ, hprev, hnext⟩

theorem mrMomentCostBase_log_le_next_scale {R Q : ℝ} (hR : 1 ≤ R)
    (hQ : 1 ≤ Q) (hRQ : Real.sqrt R ≤ Q) :
    Real.log (mrMomentCostBase R) ≤ 3 * Real.log (2 * (Q + 1)) := by
  have hR0 : 0 ≤ R := by linarith
  have hs : (Real.sqrt R) ^ 2 = R := Real.sq_sqrt hR0
  have hquad : R + 1 ≤ (Q + 1) ^ 2 := by
    nlinarith [Real.sqrt_nonneg R]
  have hlog : Real.log (R + 1) ≤ 2 * Real.log (Q + 1) := by
    have hh := Real.log_le_log (by linarith : 0 < R + 1) hquad
    simpa only [Real.log_pow, Nat.cast_ofNat] using hh
  have hlog2 : (1 : ℝ) / 2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlogQ : Real.log 2 ≤ Real.log (Q + 1) :=
    Real.log_le_log (by norm_num) (by linarith)
  unfold mrMomentCostBase
  rw [Real.log_mul (by positivity) (by linarith),
    Real.log_mul (by norm_num) (by positivity), Real.log_exp,
    Real.log_mul (by norm_num) (by linarith)]
  linarith

theorem mrLastBlock_moment_cost
    {eta p₁ q₁ : ℝ} (heta : 0 < eta) (hp : 2 ≤ p₁)
    (hq : 1 ≤ q₁) (hlogq : 1 ≤ Real.log q₁)
    (hbudget : 4096 * Real.log q₁ ≤ eta * p₁)
    {J : ℕ} (hJ : 1 ≤ J) {R : ℝ} (hR : 1 ≤ R)
    (hnext : Real.sqrt R ≤ mrLogScheduleUpper q₁ (J + 1)) :
    Real.log (mrMomentCostBase R) ≤ eta * (mrLogScheduleLower p₁ q₁ J - 1) := by
  have hQ : 1 ≤ mrLogScheduleUpper q₁ (J + 1) :=
    hq.trans (mrLogScheduleUpper_ge hq (by omega))
  have hpre := mrMomentCostBase_log_le_next_scale hR hQ hnext
  have hpJ : 2 ≤ mrLogScheduleLower p₁ q₁ J :=
    hp.trans (mrLogScheduleLower_ge (by linarith) hq hJ)
  have hsep := mrLogSchedule_shifted_cost_separation heta hp hq hlogq hbudget
    (j := J + 1) (by omega)
  simp only [Nat.add_sub_cancel] at hsep
  have hpaid := (div_le_div_iff₀ (by linarith : 0 < mrLogScheduleLower p₁ q₁ J - 1)
    (by positivity : 0 < 2 * ((J + 1 : ℕ) : ℝ) ^ 2)).mp hsep
  have hlog : 0 ≤ Real.log (2 * (mrLogScheduleUpper q₁ (J + 1) + 1)) :=
    Real.log_nonneg (by linarith)
  have hjr : (1 : ℝ) ≤ (J + 1 : ℕ) := by exact_mod_cast (by omega : 1 ≤ J + 1)
  have hsq := one_le_pow₀ (n := 2) hjr
  nlinarith [mul_nonneg (sub_nonneg.mpr hsq) hlog]

theorem mrLogBlockResolution_le_schedule
    {eta p₁ q₁ : ℝ} (heta : 0 ≤ eta) (hp : 0 ≤ p₁)
    (hq : 1 ≤ q₁) (hpq : p₁ ≤ q₁) {j : ℕ} (hj : 1 ≤ j) :
    mrLogBlockResolution eta p₁ q₁ (j : ℝ) ≤
      mrLogScheduleUpper q₁ j * Real.exp (mrLogScheduleUpper q₁ j / 6) := by
  have hsq := mrLogScheduleUpper_sq_index_le hq hj
  have hpQ : p₁ ≤ mrLogScheduleUpper q₁ j := hpq.trans (mrLogScheduleUpper_ge hq hj)
  have hlog : 0 ≤ Real.log q₁ := Real.log_nonneg hq
  have hexp : Real.exp ((1 / 6 - eta) * p₁ - Real.log q₁ / 3) ≤
      Real.exp (mrLogScheduleUpper q₁ j / 6) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg heta hp]
  unfold mrLogBlockResolution
  exact mul_le_mul hsq hexp (Real.exp_pos _).le (by linarith [sq_nonneg (j : ℝ)])

def mrNoSmallCountConstant : ℝ := 88 * Real.exp 1 * (4 + 2 * Real.pi)

theorem mrNoSmallCountConstant_pos : 0 < mrNoSmallCountConstant := by
  unfold mrNoSmallCountConstant
  positivity

theorem mrUniformNoSmallCountFactor_le_last_block
    {eta p₁ q₁ : ℝ} (heta : 0 ≤ eta) (hp : 0 ≤ p₁)
    (hq : 1 ≤ q₁) (hpq : p₁ ≤ q₁) {j : ℕ} (hj : 1 ≤ j)
    {R : ℝ} (hR : 1 ≤ R) (hjR : mrLogScheduleUpper q₁ j ≤ Real.sqrt R) :
    mrUniformNoSmallCountFactor eta p₁ q₁ j R ≤
      mrNoSmallCountConstant * R ^ 3 * Real.exp (Real.sqrt R) := by
  let Q := mrLogScheduleUpper q₁ j
  let H := mrLogBlockResolution eta p₁ q₁ (j : ℝ)
  have hQ : 1 ≤ Q := hq.trans (mrLogScheduleUpper_ge hq hj)
  have hR0 : 0 ≤ R := by linarith
  have hs0 : 0 ≤ Real.sqrt R := Real.sqrt_nonneg R
  have hs : (Real.sqrt R) ^ 2 = R := Real.sq_sqrt hR0
  have hs1 : 1 ≤ Real.sqrt R := by nlinarith
  have hsR : Real.sqrt R ≤ R := by nlinarith
  have hQsq : Q ^ 2 ≤ R := by dsimp only [Q]; nlinarith
  have hHQ : H * Q ≤ R * Real.exp (Real.sqrt R / 6) := by
    have hH := mrLogBlockResolution_le_schedule heta hp hq hpq hj
    change H ≤ Q * Real.exp (Q / 6) at hH
    calc
      _ ≤ (Q * Real.exp (Q / 6)) * Q := mul_le_mul_of_nonneg_right hH (by linarith)
      _ = Q ^ 2 * Real.exp (Q / 6) := by ring
      _ ≤ R * Real.exp (Real.sqrt R / 6) :=
        mul_le_mul hQsq (Real.exp_le_exp.mpr (by dsimp only [Q]; linarith))
          (Real.exp_pos _).le hR0
  have hlinear : 3 + 4 * R + 4 * Q ≤ 11 * R := by dsimp only [Q]; linarith
  have hB : mrMomentCostBase R ≤ 4 * Real.exp 1 * R := by
    unfold mrMomentCostBase
    nlinarith [Real.exp_pos 1]
  have hQexp : Real.exp (Q / 2) ≤ Real.exp (Real.sqrt R / 2) :=
    Real.exp_le_exp.mpr (by dsimp only [Q]; linarith)
  have h1 : 2 * H * Q * (4 + 2 * Real.pi) ≤
      2 * (R * Real.exp (Real.sqrt R / 6)) * (4 + 2 * Real.pi) := by
    have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hHQ (by norm_num : (0 : ℝ) ≤ 2))
      (show 0 ≤ 4 + 2 * Real.pi by positivity)
    simpa only [← mul_assoc] using hh
  have h2 := mul_le_mul h1 hlinear (by positivity : 0 ≤ 3 + 4 * R + 4 * Q) (by positivity)
  have h3 := mul_le_mul h2 hB (by unfold mrMomentCostBase; positivity) (by positivity)
  have h4 := mul_le_mul h3 hQexp (Real.exp_pos _).le (by positivity)
  change mrUniformNoSmallCountFactor eta p₁ q₁ j R ≤ _ at h4
  calc
    _ ≤ (2 * (R * Real.exp (Real.sqrt R / 6)) * (4 + 2 * Real.pi) *
        (11 * R)) * (4 * Real.exp 1 * R) * Real.exp (Real.sqrt R / 2) := h4
    _ = mrNoSmallCountConstant * R ^ 3 *
        Real.exp (Real.sqrt R / 6 + Real.sqrt R / 2) := by
      rw [Real.exp_add]
      unfold mrNoSmallCountConstant
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith))
      (mul_nonneg mrNoSmallCountConstant_pos.le (by positivity))

theorem mrNoSmallOptimizedCountBudget_le_last_block
    {eta p₁ q₁ : ℝ} (heta0 : 0 < eta) (heta1 : eta ≤ 1 / 12)
    (hp : 2 ≤ p₁) (hq : 1 ≤ q₁) (hpq : p₁ ≤ q₁)
    (hlogq : 1 ≤ Real.log q₁) (hbudget : 4096 * Real.log q₁ ≤ eta * p₁)
    {J : ℕ} (hJ : 1 ≤ J) {T R : ℝ} (hT : 1 ≤ T) (hR : 1 ≤ R)
    (hTR : Real.log T ≤ R) (hJR : mrLogScheduleUpper q₁ J ≤ Real.sqrt R)
    (hnext : Real.sqrt R ≤ mrLogScheduleUpper q₁ (J + 1)) :
    mrNoSmallOptimizedCountBudget eta p₁ q₁ J T ≤
      mrNoSmallCountConstant * R ^ 3 * Real.exp (Real.sqrt R) *
        Real.exp ((1 / 2 - eta) * Real.log T) := by
  have hcost := mrLastBlock_moment_cost heta0 hp hq hlogq hbudget hJ hR hnext
  have hcount := mrNoSmallOptimizedCountBudget_le_uniform heta0 heta1 hp hq hlogq hbudget
    hJ hT hR hTR hcost
  exact hcount.trans (mul_le_mul_of_nonneg_right
    (mrUniformNoSmallCountFactor_le_last_block heta0.le (by linarith) hq hpq hJ hR hJR)
    (Real.exp_pos _).le)

theorem mrArithmetic_noSmall_sample_card_le_last_block
    {eta p₁ q₁ : ℝ} (heta0 : 0 < eta) (heta1 : eta ≤ 1 / 12)
    (hp : 2 ≤ p₁) (hq : 1 ≤ q₁) (hpq : p₁ ≤ q₁)
    (hlogq : 1 ≤ Real.log q₁) (hbudget : 4096 * Real.log q₁ ≤ eta * p₁)
    {J : ℕ} (hJ : 1 ≤ J) {R : ℝ} (hR : 1 ≤ R)
    (hJR : mrLogScheduleUpper q₁ J ≤ Real.sqrt R)
    (hnext : Real.sqrt R ≤ mrLogScheduleUpper q₁ (J + 1))
    {f : ℕ → ℂ} (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (S : Finset ℝ) {T : ℝ} (hT : 1 ≤ T) (hTR : Real.log T ≤ R)
    (hST : ∀ t ∈ S, |t| ≤ T)
    (hsep : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → 1 ≤ |s - t|)
    (hU : ∀ t ∈ S, t ∈ mrNoSmallFrequencyClass (mrArithmeticSmallFrequencySet eta p₁ q₁ f) J) :
    (S.card : ℝ) ≤ mrNoSmallCountConstant * R ^ 3 * Real.exp (Real.sqrt R) *
      Real.exp ((1 / 2 - eta) * Real.log T) := by
  have hcount := mrArithmetic_noSmall_sample_card_le_optimized heta0 heta1 hp hq hlogq hbudget
    hJ le_rfl hbound S hT hST hsep hU
  exact hcount.trans (mrNoSmallOptimizedCountBudget_le_last_block heta0 heta1 hp hq hpq hlogq hbudget
    hJ hT hR hTR hJR hnext)

end

end Erdos67b
