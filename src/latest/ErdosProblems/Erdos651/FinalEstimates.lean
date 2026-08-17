/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos651.Definitions

/-!
# Numerical endgame for Erdős Problem 651

This file isolates the elementary estimates used at the end of the
Pohoata--Zakharov argument.  The geometric part of the proof only has to
produce an upper bound of the shape

`N n ≤ t n ^ (C * n / t n)`

(with real exponent), where `t n → ∞`.  The results below turn such a bound
into the `2 ^ (o(n))` formulation used in `Definitions.lean`.

We also record the concrete fourth-root cutoff used in the argument and a
small binomial-sum estimate useful when the geometric encoding is counted.
-/

namespace Erdos651

open Filter Finset Set
open scoped BigOperators Topology

noncomputable section

/-! ## The fourth-root cutoff -/

/-- The integer cutoff `⌊n^(1/4)⌋` used in the parameter choice. -/
def pzQuarterRoot (n : ℕ) : ℕ :=
  ⌊(n : ℝ) ^ (1 / 4 : ℝ)⌋₊

/-- The fourth-root cutoff is unbounded. -/
theorem pzQuarterRoot_tendsto_atTop : Tendsto pzQuarterRoot atTop atTop := by
  exact tendsto_nat_floor_atTop.comp
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp
      tendsto_natCast_atTop_atTop)

/-- In particular, every fixed integer is eventually below the cutoff. -/
theorem eventually_le_pzQuarterRoot (m : ℕ) :
    ∀ᶠ n : ℕ in atTop, m ≤ pzQuarterRoot n :=
  pzQuarterRoot_tendsto_atTop.eventually_ge_atTop m

/-! ## A binomial counting bound -/

/-- A single binomial coefficient is bounded by the corresponding power. -/
theorem choose_le_base_pow (t m : ℕ) : t.choose m ≤ t ^ m :=
  Nat.choose_le_pow t m

/-- The number of subsets of a `t`-element set having size at most `m` is
at most `t^(m+1)`, provided `m < t`. -/
theorem sum_choose_le_base_pow {t m : ℕ} (hm : m < t) :
    (∑ i ∈ range (m + 1), t.choose i) ≤ t ^ (m + 1) := by
  have ht : 1 ≤ t := by omega
  calc
    (∑ i ∈ range (m + 1), t.choose i)
        ≤ ∑ _i ∈ range (m + 1), t ^ m := by
          gcongr with i hi
          exact (Nat.choose_le_pow t i).trans
            (Nat.pow_le_pow_right ht (by simpa using (mem_range.mp hi)))
    _ = (m + 1) * t ^ m := by simp
    _ ≤ t * t ^ m := Nat.mul_le_mul_right (t ^ m) (by omega)
    _ = t ^ (m + 1) := by rw [pow_succ']

/-! ## The logarithmic loss -/

/-- The coefficient in the logarithm of `t^(C n/t)`. -/
def pzDelta (C : ℝ) (t : ℕ → ℕ) (n : ℕ) : ℝ :=
  C * (Real.log (t n : ℝ) / (t n : ℝ))

/-- For any unbounded integer parameter `t`, its logarithmic loss tends to
zero. -/
theorem pzDelta_tendsto_zero (C : ℝ) {t : ℕ → ℕ}
    (ht : Tendsto t atTop atTop) :
    Tendsto (pzDelta C t) atTop (𝓝 0) := by
  have hcast : Tendsto (fun n : ℕ ↦ (t n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp ht
  have hratio : Tendsto
      (fun n : ℕ ↦ Real.log (t n : ℝ) / (t n : ℝ)) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hcast
  change Tendsto
    (fun n : ℕ ↦ C * (Real.log (t n : ℝ) / (t n : ℝ))) atTop (𝓝 0)
  simpa only [mul_zero] using hratio.const_mul C

/-- The logarithmic loss attached to the fourth-root choice tends to zero. -/
theorem pzQuarterRoot_delta_tendsto_zero (C : ℝ) :
    Tendsto (pzDelta C pzQuarterRoot) atTop (𝓝 0) :=
  pzDelta_tendsto_zero C pzQuarterRoot_tendsto_atTop

/-! ## Conversion of the PZ envelope to base-two subexponential growth -/

/-- If `t n → ∞`, then `t^(C n/t)` is eventually smaller than
`2^(ε n)` for every `ε > 0`.  Powers in this statement are real powers. -/
theorem eventually_pzEnvelope_lt_two_rpow (C : ℝ) {t : ℕ → ℕ}
    (ht : Tendsto t atTop atTop) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      (t n : ℝ) ^ (C * (n : ℝ) / (t n : ℝ)) <
        (2 : ℝ) ^ (ε * (n : ℝ)) := by
  have htarget : 0 < ε * Real.log 2 :=
    mul_pos hε (Real.log_pos one_lt_two)
  have hsmall : ∀ᶠ n : ℕ in atTop, pzDelta C t n < ε * Real.log 2 :=
    (pzDelta_tendsto_zero C ht).eventually (Iio_mem_nhds htarget)
  filter_upwards [hsmall, ht.eventually_gt_atTop 0, eventually_gt_atTop 0]
    with n hn htpos hnpos
  rw [Real.rpow_def_of_pos (Nat.cast_pos.mpr htpos),
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  apply Real.exp_lt_exp.mpr
  calc
    Real.log (t n : ℝ) * (C * (n : ℝ) / (t n : ℝ))
        = pzDelta C t n * (n : ℝ) := by rw [pzDelta]; ring
    _ < (ε * Real.log 2) * (n : ℝ) :=
      mul_lt_mul_of_pos_right hn (Nat.cast_pos.mpr hnpos)
    _ = Real.log 2 * (ε * (n : ℝ)) := by ring

/-- A function lying below a PZ envelope has subexponential upper growth. -/
theorem hasSubexponentialUpperBound_of_pzEnvelope
    {f t : ℕ → ℕ} (C : ℝ) (ht : Tendsto t atTop atTop)
    (hf : ∀ᶠ n : ℕ in atTop,
      (f n : ℝ) ≤ (t n : ℝ) ^ (C * (n : ℝ) / (t n : ℝ))) :
    HasSubexponentialUpperBound f := by
  intro ε hε
  filter_upwards [hf, eventually_pzEnvelope_lt_two_rpow C ht hε]
    with n hfn henv
  exact hfn.trans henv.le

/-- The specialization of the envelope criterion to
`t n = ⌊n^(1/4)⌋`. -/
theorem hasSubexponentialUpperBound_of_quarterRootEnvelope
    {f : ℕ → ℕ} (C : ℝ)
    (hf : ∀ᶠ n : ℕ in atTop,
      (f n : ℝ) ≤ (pzQuarterRoot n : ℝ) ^
        (C * (n : ℝ) / (pzQuarterRoot n : ℝ))) :
    HasSubexponentialUpperBound f :=
  hasSubexponentialUpperBound_of_pzEnvelope C pzQuarterRoot_tendsto_atTop hf

end

end Erdos651
