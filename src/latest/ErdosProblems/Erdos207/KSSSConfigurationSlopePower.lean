/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.KSSSConfigurationSlopeSource
import ErdosProblems.Erdos207.KSSSUniformCountBounds
import ErdosProblems.Erdos207.ConfigurationVariancePower
import ErdosProblems.Erdos207.PowerSelectorBounds

/-! # Uniform configuration slope powers, with no division by time -/

namespace Erdos207

open Finset

noncomputable section

theorem configuration_numerator_abs_le_power
    (N t yprev ycurr alpha beta H : ℝ) (z : ℕ)
    (hN : 0 ≤ N) (ht : 2 ≤ t) (hprev0 : 0 ≤ yprev) (hcurr0 : 0 ≤ ycurr)
    (halpha : 0 ≤ alpha) (hbeta : 0 ≤ beta) (hH : 0 ≤ H)
    (hprev : yprev ≤ t * N ^ (z + 2)) (hcurr : ycurr ≤ t * N ^ (z + 1))
    (ha : alpha ≤ t) (hb : beta ≤ t) (hthreat : H ≤ t * N) :
    |alpha * yprev - beta * ycurr * H| ≤ t ^ 4 * N ^ (z + 2) := by
  calc
    _ ≤ |alpha * yprev| + |beta * ycurr * H| := abs_sub _ _
    _ = yprev * alpha + ycurr * (beta * H) := by
      rw [abs_of_nonneg (mul_nonneg halpha hprev0),
        abs_of_nonneg (mul_nonneg (mul_nonneg hbeta hcurr0) hH)]
      ring
    _ ≤ _ := configuration_move_numerator_power N t yprev ycurr alpha beta H z
      hN ht hprev0 hcurr0 halpha hbeta hH hprev hcurr ha hb hthreat

theorem ksssConfigurationSlope_succ_power
    (orders : Finset ℕ) (a : ℕ → ℝ) (E A time N t : ℝ) (d c b : ℕ)
    (hE : 0 < E) (hA : 0 < A) (htime : 0 ≤ time) (hclock : 3 * time < E)
    (horders : ∀ k ∈ orders, 1 ≤ k) (had : 0 ≤ a d) (hc : c + 2 ≤ d)
    (hN : 0 < N) (ht : 6 ≤ t) (hd : (d : ℝ) ≤ t)
    (hprev : ksssConfigurationTrajectory orders a E A d c time ≤ t * N ^ (d - c))
    (hcurr : ksssConfigurationTrajectory orders a E A d (c + 1) time ≤ t * N ^ (d - (c + 1)))
    (hH0 : 0 ≤ ksssThreatTrajectory orders a E A time)
    (hH : ksssThreatTrajectory orders a E A time ≤ t * N)
    (hden : N ^ 3 / (6 * t ^ (5 * b + 1)) ≤ ksssAvailableTrajectory orders a E A time) :
    |ksssConfigurationSlope orders a E A d (c + 1) time| ≤
      N ^ (d - (c + 1) - 1) / N * t ^ (5 * b + 6) := by
  let z := d - (c + 1) - 1
  have hp := ksssEdgeDensity_pos hE hclock
  have hAvail := ksssAvailableTrajectory_pos orders a hE hA hclock
  have hprev0 := ksssConfigurationTrajectory_nonneg orders a E A time d c hA.le htime hp.le had
  have hcurr0 := ksssConfigurationTrajectory_nonneg orders a E A time d (c + 1) hA.le htime hp.le had
  have hprevExp : d - c = z + 2 := by dsimp only [z]; omega
  have hcurrExp : d - (c + 1) = z + 1 := by dsimp only [z]; omega
  have halpha : ((d - c : ℕ) : ℝ) ≤ t := by
    calc
      _ ≤ (d : ℝ) := by exact_mod_cast Nat.sub_le d c
      _ ≤ t := hd
  have hbeta : ((d - (c + 1) : ℕ) : ℝ) ≤ t := by
    calc
      _ ≤ (d : ℝ) := by exact_mod_cast Nat.sub_le d (c + 1)
      _ ≤ t := hd
  have hnum := configuration_numerator_abs_le_power N t
    (ksssConfigurationTrajectory orders a E A d c time)
    (ksssConfigurationTrajectory orders a E A d (c + 1) time)
    (d - c : ℕ) (d - (c + 1) : ℕ) (ksssThreatTrajectory orders a E A time) z
    hN.le (by linarith) hprev0 hcurr0 (Nat.cast_nonneg _) (Nat.cast_nonneg _) hH0
    (by simpa only [hprevExp] using hprev) (by simpa only [hcurrExp] using hcurr)
    halpha hbeta hH
  rw [ksssConfigurationSlope_succ_source orders a E A time horders hE.ne' hp.ne' hAvail.ne'
    (by omega), abs_div, abs_of_pos hAvail]
  exact move_numerator_div_selector_power N t _ _ z b hN ht (abs_nonneg _) hnum hden

theorem ksssConfigurationSlope_zero_power
    (orders : Finset ℕ) (a : ℕ → ℝ) (E A time N t : ℝ) (d b : ℕ)
    (hE : 0 < E) (hA : 0 < A) (htime : 0 ≤ time) (hclock : 3 * time < E)
    (horders : ∀ k ∈ orders, 1 ≤ k) (had : 0 ≤ a d) (hd1 : 1 ≤ d)
    (hN : 0 < N) (ht : 6 ≤ t) (hd : (d : ℝ) ≤ t)
    (hcurr : ksssConfigurationTrajectory orders a E A d 0 time ≤ t * N ^ d)
    (hH0 : 0 ≤ ksssThreatTrajectory orders a E A time)
    (hH : ksssThreatTrajectory orders a E A time ≤ t * N)
    (hden : N ^ 3 / (6 * t ^ (5 * b + 1)) ≤ ksssAvailableTrajectory orders a E A time) :
    |ksssConfigurationSlope orders a E A d 0 time| ≤ N ^ (d - 1) / N * t ^ (5 * b + 6) := by
  have hp := ksssEdgeDensity_pos hE hclock
  have hAvail := ksssAvailableTrajectory_pos orders a hE hA hclock
  have hcurr0 := ksssConfigurationTrajectory_nonneg orders a E A time d 0 hA.le htime hp.le had
  have hcurrExp : d - 1 + 1 = d := by omega
  have hnum' := configuration_numerator_abs_le_power N t 0
    (ksssConfigurationTrajectory orders a E A d 0 time) 0 d (ksssThreatTrajectory orders a E A time)
    (d - 1) hN.le (by linarith) le_rfl hcurr0 le_rfl (Nat.cast_nonneg _) hH0
    (by positivity) (by simpa only [hcurrExp] using hcurr) (by linarith) hd hH
  have hnum : |(d : ℝ) * ksssConfigurationTrajectory orders a E A d 0 time *
      ksssThreatTrajectory orders a E A time| ≤ t ^ 4 * N ^ (d - 1 + 2) := by
    simpa only [zero_mul, zero_sub, abs_neg] using hnum'
  rw [ksssConfigurationSlope_zero_source orders a E A time horders hE.ne' hp.ne' hAvail.ne' hd1,
    neg_mul, neg_mul, neg_div, abs_neg, abs_div, abs_of_pos hAvail]
  exact move_numerator_div_selector_power N t _ _ (d - 1) b hN ht (abs_nonneg _) hnum hden

end

end Erdos207
