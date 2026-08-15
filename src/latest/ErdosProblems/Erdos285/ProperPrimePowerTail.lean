/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos285.PositiveReservoir

/-!
# The negligible tail of proper prime powers

The proper prime powers (prime powers of exponent at least two) have counting
function `O(sqrt x log x)`.  Partial summation therefore makes their reciprocal
sum above any cutoff tending to infinity vanish.  This file records the
quantitative estimate needed by the positive-reservoir argument for Erdős 285.
-/

open Filter Finset Real Asymptotics MeasureTheory
open scoped BigOperators Topology

namespace Erdos285.PositiveReservoir

noncomputable section

attribute [local instance] Classical.propDecidable

/-- A real-power majorant for the elementary proper-prime-power count. -/
lemma properPrimePowerCount_le_rpow (n : ℕ) :
    (properPrimePowerCount n : ℝ) ≤ 8 * (n : ℝ) ^ (3 / 4 : ℝ) := by
  by_cases hn : n = 0
  · subst n
    simp [properPrimePowerCount]
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hsqrt : (n.sqrt : ℝ) ≤ Real.sqrt (n : ℝ) := by
    rw [Real.le_sqrt (by positivity) (by positivity)]
    exact_mod_cast (show n.sqrt ^ 2 ≤ n by simpa [pow_two] using Nat.sqrt_le n)
  have hlog2 : (1 / 2 : ℝ) < Real.log 2 :=
    lt_trans (by norm_num) Real.log_two_gt_d9
  have hnatlog : (Nat.log 2 n : ℝ) ≤ 8 * (n : ℝ) ^ (1 / 4 : ℝ) := by
    calc
      (Nat.log 2 n : ℝ) ≤ Real.logb 2 n := Real.natLog_le_logb n 2
      _ = Real.log n / Real.log 2 := by rw [Real.logb]
      _ ≤ 8 * (n : ℝ) ^ (1 / 4 : ℝ) := by
        apply (div_le_iff₀ (lt_trans (by norm_num) hlog2)).2
        have hlog := Real.log_natCast_le_rpow_div n
          (show (0 : ℝ) < 1 / 4 by norm_num)
        have hrpow : 0 ≤ (n : ℝ) ^ (1 / 4 : ℝ) :=
          Real.rpow_nonneg (by positivity) _
        norm_num at hlog ⊢
        nlinarith
  have hcount : (properPrimePowerCount n : ℝ) ≤
      (n.sqrt : ℝ) * (Nat.log 2 n : ℝ) := by
    exact_mod_cast properPrimePowerCount_le n
  calc
    (properPrimePowerCount n : ℝ) ≤
        (n.sqrt : ℝ) * (Nat.log 2 n : ℝ) := hcount
    _ ≤ Real.sqrt (n : ℝ) * (8 * (n : ℝ) ^ (1 / 4 : ℝ)) := by
      gcongr
    _ = 8 * (n : ℝ) ^ (3 / 4 : ℝ) := by
      rw [Real.sqrt_eq_rpow]
      calc
        (n : ℝ) ^ (1 / 2 : ℝ) * (8 * (n : ℝ) ^ (1 / 4 : ℝ)) =
            8 * ((n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (1 / 4 : ℝ)) := by ring
        _ = 8 * (n : ℝ) ^ ((1 / 2 : ℝ) + 1 / 4) := by
          rw [Real.rpow_add hnpos]
        _ = 8 * (n : ℝ) ^ (3 / 4 : ℝ) := by norm_num

private def properPowerIndicator (n : ℕ) : ℝ :=
  if IsPrimePow n ∧ ¬ n.Prime then 1 else 0

private lemma sum_properPowerIndicator_Icc (n : ℕ) :
    ∑ q ∈ Icc 0 n, properPowerIndicator q = (properPrimePowerCount n : ℝ) := by
  rw [properPrimePowerCount]
  have hfilter : ((Icc 0 n).filter fun q ↦ IsPrimePow q ∧ ¬ q.Prime) =
      (Icc 2 n).filter fun q ↦ IsPrimePow q ∧ ¬ q.Prime := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨-, hqn⟩, hqpp, hqnprime⟩
      exact ⟨⟨hqpp.one_lt, hqn⟩, hqpp, hqnprime⟩
    · rintro ⟨⟨hq2, hqn⟩, hqpp, hqnprime⟩
      exact ⟨⟨by omega, hqn⟩, hqpp, hqnprime⟩
  calc
    ∑ q ∈ Icc 0 n, properPowerIndicator q =
        ∑ q ∈ Icc 0 n, if IsPrimePow q ∧ ¬ q.Prime then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro q hq
      simp [properPowerIndicator]
    _ = ∑ q ∈ (Icc 0 n).filter (fun q ↦ IsPrimePow q ∧ ¬ q.Prime), (1 : ℝ) := by
      rw [Finset.sum_filter]
    _ = ∑ q ∈ (Icc 2 n).filter (fun q ↦ IsPrimePow q ∧ ¬ q.Prime), (1 : ℝ) := by
      rw [hfilter]
    _ = ((Icc 2 n).filter (fun q ↦ IsPrimePow q ∧ ¬ q.Prime)).card := by
      simp only [sum_const, nsmul_eq_mul, mul_one]

private lemma properPowerIntegral_intervalIntegrable (a b : ℕ) (ha : 2 ≤ a)
    (hab : a ≤ b) :
    IntervalIntegrable
      (fun t : ℝ ↦ (properPrimePowerCount ⌊t⌋₊ : ℝ) / t ^ 2)
      MeasureTheory.volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by exact_mod_cast hab)]
  have hcont : ContinuousOn (fun t : ℝ ↦ (t ^ 2)⁻¹) (Set.Icc (a : ℝ) b) := by
    intro t ht
    exact ContinuousAt.continuousWithinAt <|
      (continuousAt_id.pow 2).inv₀ (pow_ne_zero 2 (ne_of_gt <| by
        exact lt_of_lt_of_le (by positivity) ht.1))
  have hbase : IntegrableOn (fun t : ℝ ↦ (t ^ 2)⁻¹) (Set.Icc (a : ℝ) b) :=
    hcont.integrableOn_Icc
  have hmul := integrableOn_mul_sum_Icc (m := 0) properPowerIndicator
    (show (0 : ℝ) ≤ a by positivity) hbase
  have heq :
      (fun t : ℝ ↦ (t ^ 2)⁻¹ * ∑ q ∈ Icc 0 ⌊t⌋₊, properPowerIndicator q) =
        fun t : ℝ ↦ (properPrimePowerCount ⌊t⌋₊ : ℝ) / t ^ 2 := by
    funext t
    rw [sum_properPowerIndicator_Icc]
    ring
  rw [heq] at hmul
  exact hmul

private lemma rpow_integrand_intervalIntegrable (a b : ℕ) (ha : 2 ≤ a)
    (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ ↦ 8 * t ^ (-5 / 4 : ℝ))
      MeasureTheory.volume a b := by
  refine ContinuousOn.intervalIntegrable fun t ht ↦ ?_
  have ht' : t ∈ Set.uIcc (a : ℝ) b := ht
  have ht0 : t ≠ 0 := by
    rw [Set.uIcc_of_le (by exact_mod_cast hab)] at ht'
    exact ne_of_gt (lt_of_lt_of_le (by positivity) ht'.1)
  exact ContinuousAt.continuousWithinAt <|
    continuousAt_const.mul (Real.continuousAt_rpow_const t _ (Or.inl ht0))

private lemma properPower_integrand_le {a b : ℕ} (ha : 2 ≤ a) {t : ℝ}
    (ht : t ∈ Set.Icc (a : ℝ) b) :
    (properPrimePowerCount ⌊t⌋₊ : ℝ) / t ^ 2 ≤ 8 * t ^ (-5 / 4 : ℝ) := by
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht.1
  have hfloor : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le ht0.le
  have hcount := properPrimePowerCount_le_rpow ⌊t⌋₊
  have hrpow : (⌊t⌋₊ : ℝ) ^ (3 / 4 : ℝ) ≤ t ^ (3 / 4 : ℝ) :=
    Real.rpow_le_rpow (by positivity) hfloor (by norm_num)
  calc
    (properPrimePowerCount ⌊t⌋₊ : ℝ) / t ^ 2 ≤
        (8 * (⌊t⌋₊ : ℝ) ^ (3 / 4 : ℝ)) / t ^ 2 :=
      div_le_div_of_nonneg_right hcount (sq_nonneg t)
    _ ≤ (8 * t ^ (3 / 4 : ℝ)) / t ^ 2 := by gcongr
    _ = 8 * t ^ (-5 / 4 : ℝ) := by
      rw [show t ^ 2 = t ^ (2 : ℝ) by norm_num [Real.rpow_natCast]]
      rw [div_eq_mul_inv, ← Real.rpow_neg ht0.le]
      calc
        8 * t ^ (3 / 4 : ℝ) * t ^ (-(2 : ℝ)) =
            8 * (t ^ (3 / 4 : ℝ) * t ^ (-(2 : ℝ))) := by ring
        _ = 8 * t ^ ((3 / 4 : ℝ) + -(2 : ℝ)) := by rw [Real.rpow_add ht0]
        _ = 8 * t ^ (-5 / 4 : ℝ) := by norm_num

/-- Uniform partial-summation estimate for the reciprocal tail of proper prime
powers.  Crucially, the bound depends only on the lower endpoint. -/
theorem properPrimePowerReciprocalInterval_le (a b : ℕ) (ha : 2 ≤ a)
    (hab : a ≤ b) :
    properPrimePowerReciprocalInterval a b ≤ 40 * (a : ℝ) ^ (-1 / 4 : ℝ) := by
  have haR : (0 : ℝ) < a := by positivity
  have hbR : (0 : ℝ) < b := lt_of_lt_of_le haR (by exact_mod_cast hab)
  have hleft := properPowerIntegral_intervalIntegrable a b ha hab
  have hright := rpow_integrand_intervalIntegrable a b ha hab
  have hintegral :
      (∫ t in (a : ℝ)..b,
          (properPrimePowerCount ⌊t⌋₊ : ℝ) / t ^ 2) ≤
        ∫ t in (a : ℝ)..b, 8 * t ^ (-5 / 4 : ℝ) :=
    intervalIntegral.integral_mono_on (by exact_mod_cast hab) hleft hright
      (fun t ht ↦ properPower_integrand_le ha ht)
  have hbcount := properPrimePowerCount_le_rpow b
  have hbterm : (properPrimePowerCount b : ℝ) / b ≤
      8 * (b : ℝ) ^ (-1 / 4 : ℝ) := by
    calc
      (properPrimePowerCount b : ℝ) / b ≤
          (8 * (b : ℝ) ^ (3 / 4 : ℝ)) / b :=
        div_le_div_of_nonneg_right hbcount hbR.le
      _ = 8 * (b : ℝ) ^ (-1 / 4 : ℝ) := by
        rw [div_eq_mul_inv, ← Real.rpow_neg_one]
        calc
          8 * (b : ℝ) ^ (3 / 4 : ℝ) * (b : ℝ) ^ (-(1 : ℝ)) =
              8 * ((b : ℝ) ^ (3 / 4 : ℝ) * (b : ℝ) ^ (-(1 : ℝ))) := by ring
          _ = 8 * (b : ℝ) ^ ((3 / 4 : ℝ) + -(1 : ℝ)) := by
            rw [Real.rpow_add hbR]
          _ = 8 * (b : ℝ) ^ (-1 / 4 : ℝ) := by norm_num
  have hbrpow : (b : ℝ) ^ (-1 / 4 : ℝ) ≤ (a : ℝ) ^ (-1 / 4 : ℝ) := by
    exact Real.rpow_le_rpow_of_nonpos haR (by exact_mod_cast hab) (by norm_num)
  have hintValue :
      (∫ t in (a : ℝ)..b, 8 * t ^ (-5 / 4 : ℝ)) =
        32 * ((a : ℝ) ^ (-1 / 4 : ℝ) - (b : ℝ) ^ (-1 / 4 : ℝ)) := by
    rw [intervalIntegral.integral_const_mul]
    rw [integral_rpow (Or.inr ⟨by norm_num, by
      rw [Set.uIcc_of_le (by exact_mod_cast hab)]
      simp only [Set.mem_Icc, not_and_or]
      exact Or.inl (not_le.mpr haR)⟩)]
    norm_num
    ring
  rw [properPrimePowerReciprocalInterval_eq a b ha hab]
  rw [← intervalIntegral.integral_of_le (by exact_mod_cast hab)]
  calc
    (properPrimePowerCount b : ℝ) / b - (properPrimePowerCount a : ℝ) / a +
          ∫ t in (a : ℝ)..b, (properPrimePowerCount ⌊t⌋₊ : ℝ) / t ^ 2 ≤
        (properPrimePowerCount b : ℝ) / b +
          ∫ t in (a : ℝ)..b, (properPrimePowerCount ⌊t⌋₊ : ℝ) / t ^ 2 := by
      have : 0 ≤ (properPrimePowerCount a : ℝ) / a := by positivity
      linarith
    _ ≤ 8 * (b : ℝ) ^ (-1 / 4 : ℝ) +
          ∫ t in (a : ℝ)..b, 8 * t ^ (-5 / 4 : ℝ) :=
      add_le_add hbterm hintegral
    _ = 8 * (b : ℝ) ^ (-1 / 4 : ℝ) +
          32 * ((a : ℝ) ^ (-1 / 4 : ℝ) - (b : ℝ) ^ (-1 / 4 : ℝ)) := by
      rw [hintValue]
    _ ≤ 40 * (a : ℝ) ^ (-1 / 4 : ℝ) := by
      have hbn : 0 ≤ (b : ℝ) ^ (-1 / 4 : ℝ) := Real.rpow_nonneg (by positivity) _
      nlinarith

private lemma smoothCutoff_tendsto_atTop' : Tendsto smoothCutoff atTop atTop := by
  apply tendsto_nat_floor_atTop.comp
  apply (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 5)).comp
  exact tendsto_natCast_atTop_atTop

private lemma eventually_smoothCutoff_le_floor_mul (α : ℝ) (hα : 0 < α) :
    ∀ᶠ x : ℕ in atTop, smoothCutoff x ≤ ⌊α * (x : ℝ)⌋₊ := by
  have hneg : Tendsto (fun x : ℕ ↦ (x : ℝ) ^ (-(3 / 5 : ℝ)))
      atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3 / 5)).comp
      tendsto_natCast_atTop_atTop
  have hsmall := hneg.eventually (Iio_mem_nhds hα)
  filter_upwards [hsmall, eventually_gt_atTop (0 : ℕ)] with x hxsmall hx
  apply Nat.floor_mono
  have hxpos : (0 : ℝ) < x := by positivity
  have hratio : (x : ℝ) ^ (2 / 5 : ℝ) / x =
      (x : ℝ) ^ (-(3 / 5 : ℝ)) := by
    calc
      (x : ℝ) ^ (2 / 5 : ℝ) / x =
          (x : ℝ) ^ ((2 / 5 : ℝ) - 1) := by
        symm
        simpa using Real.rpow_sub hxpos (2 / 5 : ℝ) 1
      _ = (x : ℝ) ^ (-(3 / 5 : ℝ)) := by norm_num
  rw [← div_le_iff₀ hxpos]
  rw [hratio]
  exact hxsmall.le

/-- For fixed `α > 0`, the reciprocal sum of non-prime prime powers in
`(floor (x^(2/5)), floor (αx)]` tends to zero. -/
theorem properPrimePowerReciprocalInterval_smoothCutoff_tendsto_zero
    (α : ℝ) (hα : 0 < α) :
    Tendsto
      (fun x : ℕ ↦ properPrimePowerReciprocalInterval
        (smoothCutoff x) ⌊α * (x : ℝ)⌋₊)
      atTop (nhds 0) := by
  have hcutoffCast : Tendsto (fun x : ℕ ↦ (smoothCutoff x : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp smoothCutoff_tendsto_atTop'
  have hmajor : Tendsto
      (fun x : ℕ ↦ 40 * (smoothCutoff x : ℝ) ^ (-1 / 4 : ℝ))
      atTop (nhds 0) := by
    simpa [neg_div] using ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp
      hcutoffCast).const_mul 40
  have htwo : ∀ᶠ x : ℕ in atTop, 2 ≤ smoothCutoff x :=
    smoothCutoff_tendsto_atTop'.eventually (eventually_ge_atTop 2)
  have hle := eventually_smoothCutoff_le_floor_mul α hα
  apply squeeze_zero'
  · filter_upwards with x
    simp only [properPrimePowerReciprocalInterval]
    positivity
  · filter_upwards [htwo, hle] with x hx2 hxle
    exact properPrimePowerReciprocalInterval_le _ _ hx2 hxle
  · exact hmajor

/-- A convenient numerical consequence of the vanishing proper-prime-power
tail. -/
theorem eventually_properPrimePowerReciprocalInterval_smoothCutoff_lt
    (α : ℝ) (hα : 0 < α) :
    ∀ᶠ x : ℕ in atTop,
      properPrimePowerReciprocalInterval
        (smoothCutoff x) ⌊α * (x : ℝ)⌋₊ < (1 / 100 : ℝ) :=
  (properPrimePowerReciprocalInterval_smoothCutoff_tendsto_zero α hα).eventually
    (Iio_mem_nhds (by norm_num))

end

end Erdos285.PositiveReservoir
