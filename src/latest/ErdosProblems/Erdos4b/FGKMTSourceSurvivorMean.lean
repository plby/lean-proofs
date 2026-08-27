/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTSourcePrimePopulation

/-! # Size and growth of the actual mean survivor population -/

namespace Erdos4b.FGKMT

noncomputable section

open Filter

def sourceSurvivorMean (a c : ℝ) (x : ℕ) : ℝ :=
  residueSieveDensity (sourceSmallPrimes a x) * (sourceSievingPrimes c x).card

theorem exists_sourceSurvivorMean_bounds :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ a c : ℝ, 0 < a → 0 < c →
      ∀ᶠ x : ℕ in atTop,
        A * a * c * x * Real.log (Real.log (x : ℝ)) / Real.log (x : ℝ) ≤
            sourceSurvivorMean a c x ∧
        sourceSurvivorMean a c x ≤
            B * a * c * x * Real.log (Real.log (x : ℝ)) / Real.log (x : ℝ) := by
  obtain ⟨A, B, hA, hB, hbound⟩ := exists_source_density_length_bounds
  refine ⟨A / 32, 2 * B, by positivity, by positivity, ?_⟩
  intro a c ha hc
  have hlog : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hbound a c ha hc, eventually_sourceSievingPrimes_card_bounds hc,
    hlog.eventually (eventually_gt_atTop (0 : ℝ))] with x hden hQ hL
  have hσ := residueSieveDensity_pos
    (fun p hp => (sourceSmallPrimes_prime a x p hp).one_lt)
  constructor
  · calc
      _ = (A * a * c * x * Real.log (Real.log (x : ℝ))) / (32 * Real.log (x : ℝ)) := by ring
      _ ≤ (residueSieveDensity (sourceSmallPrimes a x) * sourceIntervalLength c x) /
          (32 * Real.log (x : ℝ)) := div_le_div_of_nonneg_right hden.1 (by positivity)
      _ = residueSieveDensity (sourceSmallPrimes a x) *
          (sourceIntervalLength c x / (32 * Real.log (x : ℝ))) := by ring
      _ ≤ sourceSurvivorMean a c x := mul_le_mul_of_nonneg_left hQ.1 hσ.le
  · calc
      sourceSurvivorMean a c x ≤ residueSieveDensity (sourceSmallPrimes a x) *
          (2 * sourceIntervalLength c x / Real.log (x : ℝ)) :=
        mul_le_mul_of_nonneg_left hQ.2 hσ.le
      _ = 2 * (residueSieveDensity (sourceSmallPrimes a x) * sourceIntervalLength c x) /
          Real.log (x : ℝ) := by ring
      _ ≤ 2 * (B * a * c * x * Real.log (Real.log (x : ℝ))) / Real.log (x : ℝ) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hden.2 (by norm_num)) hL.le
      _ = _ := by ring

theorem eventually_sourceSurvivorMean_ge_log_pow {a c : ℝ} (ha : 0 < a) (hc : 0 < c)
    (j : ℕ) : ∀ᶠ x : ℕ in atTop, Real.log (x : ℝ) ^ j ≤ sourceSurvivorMean a c x := by
  obtain ⟨A, _B, hA, _hB, hbound⟩ := exists_sourceSurvivorMean_bounds
  have hlog : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloglog := Real.tendsto_log_atTop.comp hlog
  have hsmall := ((isLittleO_log_rpow_rpow_atTop ((j + 1 : ℕ) : ℝ)
    (by norm_num : (0 : ℝ) < 1)).comp_tendsto
      (tendsto_natCast_atTop_atTop (R := ℝ))).def (mul_pos (mul_pos hA ha) hc)
  filter_upwards [hbound a c ha hc, hsmall,
    hlog.eventually (eventually_gt_atTop (0 : ℝ)),
    hloglog.eventually (eventually_ge_atTop (1 : ℝ))] with x hmean hs hL hl
  have hbudget : Real.log (x : ℝ) ^ (j + 1) ≤ A * a * c * x := by
    simpa only [Function.comp_apply, Real.rpow_natCast, Real.rpow_one, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg hL.le (j + 1)),
      abs_of_nonneg (Nat.cast_nonneg x : (0 : ℝ) ≤ x)] using hs
  calc
    Real.log (x : ℝ) ^ j ≤ (A * a * c * x) / Real.log (x : ℝ) := by
      apply (le_div_iff₀ hL).mpr
      simpa only [pow_succ] using hbudget
    _ ≤ A * a * c * x * Real.log (Real.log (x : ℝ)) / Real.log (x : ℝ) :=
      div_le_div_of_nonneg_right (le_mul_of_one_le_right (by positivity) hl) hL.le
    _ ≤ _ := hmean.1

end

end Erdos4b.FGKMT
