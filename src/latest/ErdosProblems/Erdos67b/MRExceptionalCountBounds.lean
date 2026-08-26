import ErdosProblems.Erdos67b.MRExceptionalSmallPrimeEnergy

/-!
# Uniform time dependence in exceptional sample counts

The factorial surrogate is absorbed using an explicit logarithmic cost
condition. Every factor independent of the sample time range remains
visible; choosing the final block from the product scale is still required.
-/

open scoped BigOperators
open Finset

namespace Erdos67b

noncomputable section

def mrMomentCostBase (R : ℝ) : ℝ := 2 * Real.exp 1 * (R + 1)

theorem mrMomentCostBase_one_le {R : ℝ} (hR : 1 ≤ R) : 1 ≤ mrMomentCostBase R := by
  have he : 1 ≤ Real.exp 1 := Real.one_le_exp_iff.mpr (by norm_num)
  unfold mrMomentCostBase
  nlinarith

/-- Absorb the integer moment cost without taking the logarithm of its
order, so the `T=1`, order-zero case remains valid. -/
theorem mrCeil_logRatio_cost_le
    {T v R sigma : ℝ} (hT : 1 ≤ T) (hv : 1 ≤ v) (hR : 1 ≤ R)
    (hTR : Real.log T ≤ R) (hcost : Real.log (mrMomentCostBase R) ≤ sigma * v) :
    (2 * Real.exp 1 * (⌈Real.log T / v⌉₊ : ℝ)) ^ ⌈Real.log T / v⌉₊ ≤
      mrMomentCostBase R * Real.exp (sigma * Real.log T) := by
  let k : ℕ := ⌈Real.log T / v⌉₊
  let B : ℝ := mrMomentCostBase R
  have hv0 : 0 < v := by linarith
  have hs : 0 ≤ Real.log T := Real.log_nonneg hT
  have hB1 : 1 ≤ B := mrMomentCostBase_one_le hR
  have hB0 : 0 < B := by linarith
  have hlogB : 0 ≤ Real.log B := Real.log_nonneg hB1
  have hk : (k : ℝ) ≤ Real.log T / v + 1 :=
    (Nat.ceil_lt_add_one (div_nonneg hs hv0.le)).le
  have hkR : (k : ℝ) ≤ R + 1 := by
    have hdiv := div_le_self hs hv
    linarith
  have hlogRatio : Real.log B / v ≤ sigma := (div_le_iff₀ hv0).mpr hcost
  have hbudget : (k : ℝ) * Real.log B ≤ sigma * Real.log T + Real.log B := by
    calc
      _ ≤ (Real.log T / v + 1) * Real.log B := mul_le_mul_of_nonneg_right hk hlogB
      _ = Real.log T * (Real.log B / v) + Real.log B := by ring
      _ ≤ Real.log T * sigma + Real.log B := add_le_add (mul_le_mul_of_nonneg_left hlogRatio hs) le_rfl
      _ = _ := by ring
  calc
    _ ≤ B ^ k := pow_le_pow_left₀ (by positivity)
      (mul_le_mul_of_nonneg_left hkR (by positivity : 0 ≤ 2 * Real.exp 1)) k
    _ = Real.exp ((k : ℝ) * Real.log B) := by rw [Real.exp_nat_mul, Real.exp_log hB0]
    _ ≤ Real.exp (sigma * Real.log T + Real.log B) := Real.exp_le_exp.mpr hbudget
    _ = _ := by rw [Real.exp_add, Real.exp_log hB0]; ring

theorem mrOptimizedPrimeSampleBudget_le_uniform
    {T v R sigma alpha : ℝ} (hT : 1 ≤ T) (hv : 1 ≤ v) (hR : 1 ≤ R)
    (hTR : Real.log T ≤ R) (hcost : Real.log (mrMomentCostBase R) ≤ sigma * v) :
    mrOptimizedPrimeSampleBudget T v alpha ≤
      (4 + 2 * Real.pi) * (3 + 4 * R + 4 * v) * mrMomentCostBase R *
        Real.exp (2 * alpha * v) * Real.exp ((2 * alpha + sigma) * Real.log T) := by
  let k : ℕ := ⌈Real.log T / v⌉₊
  have hk := (mrCeil_logRatio_bounds hT (by linarith : 0 < v)).2
  have hkR : (k : ℝ) ≤ (k : ℝ) * v := by nlinarith [show (0 : ℝ) ≤ k by positivity]
  have hpre : 3 + 2 * (k : ℝ) * (v + 1) ≤ 3 + 4 * R + 4 * v := by
    change (k : ℝ) * v ≤ Real.log T + v at hk
    nlinarith
  have hpower := mrCeil_logRatio_cost_le hT hv hR hTR hcost
  have hfirst := mul_le_mul_of_nonneg_left hpre
    (show 0 ≤ 4 + 2 * Real.pi by positivity)
  have hproduct := mul_le_mul hfirst hpower (by positivity) (by positivity)
  calc
    _ ≤ ((4 + 2 * Real.pi) * (3 + 4 * R + 4 * v)) *
        (mrMomentCostBase R * Real.exp (sigma * Real.log T)) *
          Real.exp (2 * alpha * (Real.log T + v)) :=
      mul_le_mul_of_nonneg_right hproduct (Real.exp_pos _).le
    _ = _ := by
      rw [show (2 * alpha + sigma) * Real.log T = 2 * alpha * Real.log T + sigma * Real.log T by ring,
        Real.exp_add,
        show 2 * alpha * (Real.log T + v) = 2 * alpha * Real.log T + 2 * alpha * v by ring,
        Real.exp_add]
      ring

theorem mrThresholdExponent_le_quarter_sub_eta {eta : ℝ} (heta : 0 ≤ eta) (j : ℕ) :
    mrThresholdExponent eta (j : ℝ) ≤ 1 / 4 - eta := by
  have hh : 0 ≤ eta * (1 / (2 * (j : ℝ))) := by positivity
  unfold mrThresholdExponent
  nlinarith

/-- The prefactor is independent of `T` once its logarithm is bounded by `R`. -/
def mrUniformNoSmallCountFactor (eta p₁ q₁ : ℝ) (j : ℕ) (R : ℝ) : ℝ :=
  2 * mrLogBlockResolution eta p₁ q₁ (j : ℝ) * mrLogScheduleUpper q₁ j *
    (4 + 2 * Real.pi) * (3 + 4 * R + 4 * mrLogScheduleUpper q₁ j) *
      mrMomentCostBase R * Real.exp (mrLogScheduleUpper q₁ j / 2)

theorem mrNoSmallOptimizedCountBudget_le_uniform
    {eta p₁ q₁ : ℝ} (heta0 : 0 < eta) (heta1 : eta ≤ 1 / 12)
    (hp : 2 ≤ p₁) (hq : 1 ≤ q₁) (hlogq : 1 ≤ Real.log q₁)
    (hbudget : 4096 * Real.log q₁ ≤ eta * p₁)
    {j : ℕ} (hj : 1 ≤ j) {T R : ℝ} (hT : 1 ≤ T) (hR : 1 ≤ R)
    (hTR : Real.log T ≤ R)
    (hcost : Real.log (mrMomentCostBase R) ≤ eta * (mrLogScheduleLower p₁ q₁ j - 1)) :
    mrNoSmallOptimizedCountBudget eta p₁ q₁ j T ≤
      mrUniformNoSmallCountFactor eta p₁ q₁ j R * Real.exp ((1 / 2 - eta) * Real.log T) := by
  let H : ℝ := mrLogBlockResolution eta p₁ q₁ (j : ℝ)
  let Q : ℝ := mrLogScheduleUpper q₁ j
  let alpha : ℝ := mrThresholdExponent eta (j : ℝ)
  let C : ℝ := (4 + 2 * Real.pi) * (3 + 4 * R + 4 * Q) *
    mrMomentCostBase R * Real.exp (Q / 2) * Real.exp ((1 / 2 - eta) * Real.log T)
  have hH : 1 ≤ H := mrLogSchedule_resolution_one_le heta1 (by linarith) hlogq hbudget hj
  have hQ : 1 ≤ Q := hq.trans (mrLogScheduleUpper_ge hq hj)
  have hB : 0 ≤ mrMomentCostBase R := (mrMomentCostBase_one_le hR).trans' (by norm_num)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hbeta := mrThresholdExponent_bounds heta0.le (by linarith) (by exact_mod_cast hj : (1 : ℝ) ≤ j)
  have hbetap := mrThresholdExponent_le_quarter_sub_eta heta0.le j
  have hs : 0 ≤ Real.log T := Real.log_nonneg hT
  have hpoint (r : ℕ) (hr : r ∈ mrScheduledSubblocks eta p₁ q₁ j) :
      mrOptimizedPrimeSampleBudget T (mrScheduledParameter eta p₁ q₁ j r) alpha ≤ C := by
    let v : ℝ := mrScheduledParameter eta p₁ q₁ j r
    have hvbounds := mrScheduledParameter_bounds heta1 hp hq hlogq hbudget hj hr
    have hpj := mrLogScheduleLower_ge (by linarith : 0 ≤ p₁) hq hj
    have hv : 1 ≤ v := by dsimp only [v]; linarith
    have hvQ : v ≤ Q := hvbounds.2
    have hcostv : Real.log (mrMomentCostBase R) ≤ eta * v :=
      hcost.trans (mul_le_mul_of_nonneg_left hvbounds.1 heta0.le)
    have hmain := mrOptimizedPrimeSampleBudget_le_uniform (alpha := alpha) hT hv hR hTR hcostv
    have hpre : 3 + 4 * R + 4 * v ≤ 3 + 4 * R + 4 * Q := by linarith
    have hexp : Real.exp (2 * alpha * v) ≤ Real.exp (Q / 2) := by
      apply Real.exp_le_exp.mpr
      change 0 ≤ alpha ∧ alpha ≤ 1 / 4 at hbeta
      nlinarith
    have htime : Real.exp ((2 * alpha + eta) * Real.log T) ≤
        Real.exp ((1 / 2 - eta) * Real.log T) := by
      apply Real.exp_le_exp.mpr
      change alpha ≤ 1 / 4 - eta at hbetap
      exact mul_le_mul_of_nonneg_right (by linarith) hs
    apply hmain.trans
    have h1 := mul_le_mul_of_nonneg_left hpre (show 0 ≤ 4 + 2 * Real.pi by positivity)
    have h2 := mul_le_mul_of_nonneg_right h1 hB
    have h3 := mul_le_mul h2 hexp (by positivity) (by positivity)
    exact mul_le_mul h3 htime (by positivity) (by positivity)
  have hcard : ((mrScheduledSubblocks eta p₁ q₁ j).card : ℝ) ≤ 2 * H * Q :=
    card_mrLogBlockIndices_le (by nlinarith)
  calc
    _ ≤ ∑ _r ∈ mrScheduledSubblocks eta p₁ q₁ j, C := Finset.sum_le_sum hpoint
    _ = ((mrScheduledSubblocks eta p₁ q₁ j).card : ℝ) * C := by simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 * H * Q) * C := mul_le_mul_of_nonneg_right hcard hC
    _ = _ := by unfold mrUniformNoSmallCountFactor; dsimp only [H, Q, C]; ring

/-- Actual no-small-class samples now have the explicit
`T^(1/2-eta)` dependence, under the stated scalar scale condition. -/
theorem mrArithmetic_noSmall_sample_card_le_uniform
    {eta p₁ q₁ : ℝ} (heta0 : 0 < eta) (heta1 : eta ≤ 1 / 12)
    (hp : 2 ≤ p₁) (hq : 1 ≤ q₁) (hlogq : 1 ≤ Real.log q₁)
    (hbudget : 4096 * Real.log q₁ ≤ eta * p₁)
    {J j : ℕ} (hj : 1 ≤ j) (hjJ : j ≤ J) {R : ℝ} (hR : 1 ≤ R)
    (hcost : Real.log (mrMomentCostBase R) ≤ eta * (mrLogScheduleLower p₁ q₁ j - 1))
    {f : ℕ → ℂ} (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (S : Finset ℝ) {T : ℝ} (hT : 1 ≤ T) (hTR : Real.log T ≤ R)
    (hST : ∀ t ∈ S, |t| ≤ T)
    (hsep : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → 1 ≤ |s - t|)
    (hU : ∀ t ∈ S, t ∈ mrNoSmallFrequencyClass (mrArithmeticSmallFrequencySet eta p₁ q₁ f) J) :
    (S.card : ℝ) ≤ mrUniformNoSmallCountFactor eta p₁ q₁ j R * Real.exp ((1 / 2 - eta) * Real.log T) := by
  have hcount := mrArithmetic_noSmall_sample_card_le_optimized heta0 heta1 hp hq hlogq hbudget
    hj hjJ hbound S hT hST hsep hU
  exact hcount.trans (mrNoSmallOptimizedCountBudget_le_uniform heta0 heta1 hp hq hlogq hbudget
    hj hT hR hTR hcost)

end

end Erdos67b
