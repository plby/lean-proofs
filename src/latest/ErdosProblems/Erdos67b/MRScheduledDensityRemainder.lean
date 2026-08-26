import ErdosProblems.Erdos67b.MRLastBlockRemainder

/-! # Paying the growing-family sieve remainder before the final index -/

open Filter
open scoped Topology

namespace Erdos67b

noncomputable section

theorem mrScheduled_sieveExponent_le_half (S : ℕ) {L : ℝ}
    (hL : 0 ≤ L) (hscale : (4 * (S : ℝ)) ^ 2 ≤ L) :
    2 * (S : ℝ) * Real.sqrt L ≤ L / 2 := by
  have hroot := Real.le_sqrt_of_sq_le hscale
  have hh := mul_le_mul_of_nonneg_right hroot (Real.sqrt_nonneg L)
  nlinarith [Real.sq_sqrt hL]

theorem mrTendsto_log_half_power_tail :
    Tendsto (fun X : ℕ ↦ Real.log (X : ℝ) * Real.exp (-Real.log (X : ℝ) / 2))
      atTop (𝓝 0) := by
  have hh := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (1 / 2)
    (by norm_num : (0 : ℝ) < 1 / 2)).comp EulerSubpower.tendsto_log_nat_atTop
  apply hh.congr'
  filter_upwards [] with X
  simp only [Function.comp_apply, Real.rpow_one]
  congr 2
  ring

theorem mrEventually_scheduled_sieveRemainder_small (S : ℕ) {delta : ℝ}
    (hdelta : 0 < delta) :
    ∀ᶠ X : ℕ in atTop, 2 ≤ X ∧ 1 ≤ Real.log (X : ℝ) ∧
      Real.log (X : ℝ) * Real.exp (2 * (S : ℝ) * Real.sqrt (Real.log (X : ℝ))) ≤
        delta * X := by
  filter_upwards [eventually_ge_atTop 2,
    EulerSubpower.tendsto_log_nat_atTop.eventually (eventually_ge_atTop 1),
    EulerSubpower.tendsto_log_nat_atTop.eventually (eventually_ge_atTop ((4 * (S : ℝ)) ^ 2)),
    mrTendsto_log_half_power_tail.eventually (gt_mem_nhds hdelta)]
    with X hX hlog hscale hsmall
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hpaid := mrScheduled_sieveExponent_le_half S (by linarith) hscale
  refine ⟨hX, hlog, ?_⟩
  apply (div_le_iff₀ hXpos).1
  calc
    _ ≤ Real.log (X : ℝ) * Real.exp (Real.log (X : ℝ) / 2) / X := by gcongr
    _ = Real.log (X : ℝ) * Real.exp (-Real.log (X : ℝ) / 2) := by
      rw [show -Real.log (X : ℝ) / 2 =
        Real.log (X : ℝ) / 2 - Real.log (X : ℝ) by ring,
        Real.exp_sub, Real.exp_log hXpos]
      ring
    _ ≤ delta := hsmall.le

end

end Erdos67b
