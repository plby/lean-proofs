import Mathlib

/-!
# The endpoint of Erdős Problem 140

This file identifies the literal extremal function on `{1, ..., N}` with
Mathlib's `rothNumberNat`, and records the elementary analytic implication
from a stretched-exponential Kelley--Meka bound to every logarithmic saving.
-/

open Filter Finset
open scoped Topology

namespace Erdos140

/-- The largest cardinality of a three-term-progression-free subset of
`{1, ..., N}`. -/
noncomputable def r3 (N : ℕ) : ℕ :=
  addRothNumber (Finset.Icc 1 N)

/-- The interval convention in `r3` agrees exactly with Mathlib's convention
`rothNumberNat N = addRothNumber (range N)`. -/
theorem r3_eq_rothNumberNat (N : ℕ) : r3 N = rothNumberNat N := by
  rw [r3, ← Finset.Ico_add_one_right_eq_Icc, addRothNumber_Ico]
  simp

/-- A positive stretched exponential in `log N` beats every fixed real power
of `log N`.  This is the analytic core of the last step in Problem 140. -/
theorem tendsto_log_rpow_mul_stretchedExp
    {c beta : ℝ} (hc : 0 < c) (hbeta : 0 < beta) (C : ℝ) :
    Tendsto
      (fun N : ℕ =>
        (Real.log (N : ℝ)) ^ C *
          Real.exp (-c * (Real.log (N : ℝ)) ^ beta))
      atTop (nhds 0) := by
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hpow : Tendsto (fun N : ℕ => (Real.log (N : ℝ)) ^ beta) atTop atTop :=
    (tendsto_rpow_atTop hbeta).comp hlog
  have h :=
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (C / beta) c hc).comp hpow
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 1] with N hN
  have hlog_nonneg : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hN.le)
  change
    ((Real.log (N : ℝ)) ^ beta) ^ (C / beta) *
        Real.exp (-c * (Real.log (N : ℝ)) ^ beta) =
      (Real.log (N : ℝ)) ^ C *
        Real.exp (-c * (Real.log (N : ℝ)) ^ beta)
  congr 1
  rw [← Real.rpow_mul hlog_nonneg]
  congr 1
  field_simp [hbeta.ne']

/-- Eventual Kelley--Meka decay implies the exact `IsBigO` conclusion used in
Erdős Problem 140.  Constants `K`, `c`, and `beta` are independent of `N`;
the Kelley--Meka theorem supplies positive `c` and `beta` (in particular one
may take `beta = 1 / 12`). -/
theorem isBigO_r3_log_rpow_of_stretchedExp
    {K c beta : ℝ} (hK : 0 ≤ K) (hc : 0 < c) (hbeta : 0 < beta)
    (hKM : ∀ᶠ N : ℕ in atTop,
      (r3 N : ℝ) ≤
        K * (N : ℝ) * Real.exp (-c * (Real.log (N : ℝ)) ^ beta))
    (C : ℝ) :
    (fun N : ℕ => (r3 N : ℝ)) =O[atTop]
      (fun N : ℕ => (N : ℝ) / (Real.log (N : ℝ)) ^ C) := by
  have hdecay :=
    tendsto_log_rpow_mul_stretchedExp hc hbeta C
  have hsmall : ∀ᶠ N : ℕ in atTop,
      (Real.log (N : ℝ)) ^ C *
          Real.exp (-c * (Real.log (N : ℝ)) ^ beta) ≤ 1 :=
    hdecay.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1))
  refine Asymptotics.IsBigO.of_bound K ?_
  filter_upwards [hKM, hsmall, eventually_gt_atTop 1] with N hbound hsmallN hN
  have hN_nonneg : 0 ≤ (N : ℝ) := by positivity
  have hlog_pos : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast hN)
  have hlogpow_pos : 0 < (Real.log (N : ℝ)) ^ C :=
    Real.rpow_pos_of_pos hlog_pos C
  rw [Real.norm_of_nonneg (Nat.cast_nonneg (r3 N))]
  rw [Real.norm_of_nonneg (div_nonneg hN_nonneg hlogpow_pos.le)]
  apply hbound.trans
  have hexp_le :
      Real.exp (-c * (Real.log (N : ℝ)) ^ beta) ≤
        1 / (Real.log (N : ℝ)) ^ C := by
    rw [le_div_iff₀ hlogpow_pos]
    simpa [mul_comm] using hsmallN
  calc
    K * (N : ℝ) * Real.exp (-c * (Real.log (N : ℝ)) ^ beta) ≤
        K * (N : ℝ) * (1 / (Real.log (N : ℝ)) ^ C) :=
      mul_le_mul_of_nonneg_left hexp_le (mul_nonneg hK hN_nonneg)
    _ = K * ((N : ℝ) / (Real.log (N : ℝ)) ^ C) := by ring

#print axioms r3_eq_rothNumberNat
#print axioms tendsto_log_rpow_mul_stretchedExp
#print axioms isBigO_r3_log_rpow_of_stretchedExp

end Erdos140
