/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The dyadic strong law for distinct roots in the positive half of the unit interval.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.CentralStrongLaw
import ErdosProblems.Erdos521.LeftTrim
import ErdosProblems.Erdos521.RightTrim
import ErdosProblems.Erdos521.InteriorDecomposition

namespace Erdos521

open MeasureTheory Filter
open scoped Topology

theorem positiveRootCount_le_central_decomposition (ε : ℕ → ℝ) (n : ℕ)
    {a b c d : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) :
    intervalRootCount ε n 0 1 ≤ smallRootCount ε n a + intervalRootCount ε n a b +
      intervalRootCount ε n b c + intervalRootCount ε n c d + intervalRootCount ε n d 1 := by
  have h := positiveRootCount_le_decomposition ε n a d
  have h₁ := intervalRootCount_split ε n hab (hbc.trans hcd)
  have h₂ := intervalRootCount_split ε n hbc hcd
  omega

theorem ae_positiveRootCount_dyadic_div_log_limit :
    ∀ᵐ ε ∂sequenceLaw, Tendsto (fun j : ℕ ↦
      (intervalRootCount ε (2 ^ j) 0 1 : ℝ) / Real.log ((2 ^ j : ℕ) : ℝ))
      atTop (𝓝 (1 / (2 * Real.pi))) := by
  have hC : 0 ≤ localMomentBulkConstant 4 := (localMomentBulkConstant_pos 4).le
  filter_upwards [ae_centralRootCount_div_log_limit, ae_left_trim_div_index_tendsto_zero,
    ae_right_trim_div_index_tendsto_zero, ae_smallRootCount_div_log_tendsto_zero,
    ae_endpointRootCount_div_log_tendsto_zero hC] with ε hcentral hleft hright hsmall hend
  have hdegree : Tendsto (fun j : ℕ ↦ (2 : ℕ) ^ j) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hs := (hsmall (dyadicPoint 4) (by norm_num [dyadicPoint]) (dyadicPoint_lt_one 4)).comp hdegree
  have he := hend.comp hdegree
  have hl := tendsto_div_log_two_pow_of_div_index hleft
  have hr := tendsto_div_log_two_pow_of_div_index hright
  simp only [zero_div] at hl hr
  have hsum := (((hs.add hl).add hcentral).add hr).add he
  simp only [zero_add, add_zero] at hsum
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hcentral hsum
  · apply Eventually.of_forall
    intro j
    have hlo : 0 ≤ dyadicPoint (Nat.sqrt j) := by
      simpa only [dyadicPoint, pow_zero, div_one, sub_self] using dyadicPoint_mono (Nat.zero_le (Nat.sqrt j))
    have hcount : (centralRootCount ε j : ℝ) ≤ (intervalRootCount ε (2 ^ j) 0 1 : ℝ) := by
      exact_mod_cast intervalRootCount_mono ε (2 ^ j) hlo (dyadicPoint_lt_one (j - Nat.sqrt j)).le
    exact div_le_div_of_nonneg_right hcount (Real.log_nonneg (by exact_mod_cast (show 1 ≤ (2 : ℕ) ^ j from Nat.one_le_two_pow)))
  · filter_upwards [eventually_central_end_le_endpoint (localMomentBulkConstant 4),
      eventually_ge_atTop 25] with j hboundary hj
    have hr₅ : 5 ≤ Nat.sqrt j := Nat.le_sqrt.mpr hj
    have hrend := (central_bin_endpoints_strict (show 9 ≤ j by omega)).le
    have hcount := positiveRootCount_le_central_decomposition ε (2 ^ j)
      (dyadicPoint_mono (show 4 ≤ Nat.sqrt j by omega)) (dyadicPoint_mono hrend) hboundary
    have hcount' : (intervalRootCount ε (2 ^ j) 0 1 : ℝ) ≤
        (smallRootCount ε (2 ^ j) (dyadicPoint 4) : ℝ) +
        (intervalRootCount ε (2 ^ j) (dyadicPoint 4) (dyadicPoint (Nat.sqrt j)) : ℝ) +
        (centralRootCount ε j : ℝ) +
        (intervalRootCount ε (2 ^ j) (dyadicPoint (j - Nat.sqrt j))
          (endpointCenter (localMomentBulkConstant 4) (2 ^ j)) : ℝ) +
        (intervalRootCount ε (2 ^ j) (endpointCenter (localMomentBulkConstant 4) (2 ^ j)) 1 : ℝ) := by
      exact_mod_cast hcount
    have hlog : 0 ≤ Real.log ((2 ^ j : ℕ) : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ (2 : ℕ) ^ j from Nat.one_le_two_pow))
    simpa only [add_div, Function.comp_apply] using div_le_div_of_nonneg_right hcount' hlog

end Erdos521
