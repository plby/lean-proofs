/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.RankinDyadicEnvelope
import ErdosProblems.Erdos4b.SourceUnconditionalDyadicCovers

/-!
# The literal prime-index threshold below the CRT endpoint

Every small index is included in a finite exceptional initial segment.
Thus no convention for logarithms at zero or negative arguments is used
to weaken the requested theorem.
-/

namespace Erdos4b.SmoothParameters

noncomputable section

open Filter
open scoped BigOperators Topology

theorem tendsto_dyadicIntervalLength_atTop (a : ℕ) :
    Tendsto (fun r : ℕ ↦ (intervalLength a r : ℝ)) atTop atTop := by
  have hX : Tendsto (fun r : ℕ ↦ (primaryFrontier a r : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_dyadicPrimaryFrontier_atTop a)
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [hX.eventually (eventually_ge_atTop b), eventually_ge_atTop 1] with r hr hrone
  apply hr.trans
  have hn : primaryFrontier a r ≤ intervalLength a r := by
    exact (Nat.le_mul_of_pos_right _ (core_pos r)).trans
      (Nat.le_mul_of_pos_right _ (by omega : 0 < r))
  exact_mod_cast hn

theorem eventually_log_index_lt_three_primary (a B : ℕ) (hB : 0 < B) :
    ∀ᶠ r in atTop, ∀ n : ℕ, 0 < n → n < B * primorial (primaryFrontier a r) →
      Real.log n < 3 * (primaryFrontier a r : ℝ) := by
  have hX : Tendsto (fun r : ℕ ↦ (primaryFrontier a r : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_dyadicPrimaryFrontier_atTop a)
  have hpnt := (tendsto_dyadicPrimaryFrontier_atTop a).eventually eventually_log_primorial_lt_two_mul
  filter_upwards [hpnt, hX.eventually (eventually_ge_atTop (Real.log B))] with r hp hBsmall
  intro n hn hnupper
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hBreal : (0 : ℝ) < B := by exact_mod_cast hB
  have hpReal : (0 : ℝ) < primorial (primaryFrontier a r) := by exact_mod_cast primorial_pos _
  have hh := Real.log_le_log hnreal
    (show (n : ℝ) ≤ (B : ℝ) * primorial (primaryFrontier a r) by exact_mod_cast hnupper.le)
  rw [Real.log_mul hBreal.ne' hpReal.ne'] at hh
  linarith

theorem exists_dyadicMultiplier_threshold_bound (a : ℕ) {C : ℝ} (hC : 0 < C) :
    ∃ D : ℕ, 0 < D ∧ ∀ B : ℕ, 0 < B →
      ∀ᶠ r in atTop, ∀ n : ℕ, n < B * primorial (primaryFrontier a r) →
        threshold C n < (D * intervalLength a r : ℕ) := by
  obtain ⟨D, hD⟩ := exists_nat_gt (max (1 : ℝ) (C * (288 * (2 : ℝ) ^ a)))
  have hDone : (1 : ℝ) < D := (le_max_left _ _).trans_lt hD
  have hDmain : C * (288 * (2 : ℝ) ^ a) < D := (le_max_right _ _).trans_lt hD
  have hDpos : 0 < D := by exact_mod_cast (lt_trans (by norm_num : (0 : ℝ) < 1) hDone)
  refine ⟨D, hDpos, ?_⟩
  intro B hB
  have hlogs : Tendsto (fun n : ℕ ↦ Real.log (Real.log n)) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    ((hlogs.eventually (eventually_ge_atTop (Real.exp 2))).and (eventually_ge_atTop 2))
  let M : ℝ := ∑ n ∈ Finset.range N, |threshold C n|
  have hsmall : ∀ n : ℕ, n < N → threshold C n ≤ M := by
    intro n hn
    exact (le_abs_self _).trans
      (Finset.single_le_sum (fun i _ ↦ abs_nonneg (threshold C i)) (Finset.mem_range.mpr hn))
  have hlargeU := (tendsto_dyadicIntervalLength_atTop a).eventually (eventually_gt_atTop M)
  filter_upwards [eventually_log_index_lt_three_primary a B hB, hlargeU,
    eventually_ge_atTop 4, eventually_ge_atTop (a + 1)] with r hrlog hrU hr4 hra
  intro n hn
  have hU : (0 : ℝ) < intervalLength a r := by
    exact_mod_cast Nat.mul_pos (Nat.mul_pos (primaryFrontier_pos a r) (core_pos r))
      (show 0 < r by omega)
  by_cases hnlarge : N ≤ n
  · have hdata := hN n hnlarge
    have hnreal : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
    have hcmp := threshold_le_rankinEnvelope hC.le hnreal hdata.1
      (hrlog n (by omega : 0 < n) hn).le
    have henv := mul_le_mul_of_nonneg_left (dyadic_rankin_envelope_le hr4 hra) hC.le
    have hbound : threshold C n ≤ (C * (288 * (2 : ℝ) ^ a)) * (intervalLength a r : ℝ) := by
      calc
        _ ≤ C * (3 * (primaryFrontier a r : ℝ)) * rankinFactor (dyadicIndexLog a r) := hcmp
        _ = C * ((3 * (primaryFrontier a r : ℝ)) * rankinFactor (dyadicIndexLog a r)) := by ring
        _ ≤ C * ((288 * (2 : ℝ) ^ a) * (intervalLength a r : ℝ)) := henv
        _ = _ := by ring
    have hh := hbound.trans_lt (mul_lt_mul_of_pos_right hDmain hU)
    simpa only [Nat.cast_mul] using hh
  · have hh := (hsmall n (by omega)).trans_lt hrU
    have hle : (intervalLength a r : ℝ) ≤ (D : ℝ) * intervalLength a r := by
      nlinarith
    exact hh.trans_le (by simpa only [Nat.cast_mul] using hle)

end

end Erdos4b.SmoothParameters
