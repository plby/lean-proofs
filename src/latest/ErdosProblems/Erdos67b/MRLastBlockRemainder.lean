import ErdosProblems.Erdos67b.MRLastBlock
import ErdosProblems.Erdos67b.EulerSubpower

/-! # Uniform final-index error on the actual growing schedule -/

open Filter
open scoped Topology

namespace Erdos67b

noncomputable section

theorem mrLastBlock_index_le_log {q L : ℝ} (hq : 1 ≤ q) (hL : 1 ≤ L)
    {J : ℕ} (hJ : 1 ≤ J) (hupper : mrLogScheduleUpper q J ≤ Real.sqrt L) :
    (J : ℝ) ≤ L := by
  have hs := (mrLogScheduleUpper_sq_index_le hq hJ).trans hupper
  have hJr : (1 : ℝ) ≤ J := by exact_mod_cast hJ
  have hJtwo : (J : ℝ) ≤ (J : ℝ) ^ 2 := by nlinarith
  have hsqrtOne : 1 ≤ Real.sqrt L := hJr.trans (hJtwo.trans hs)
  have hsqrtLe : Real.sqrt L ≤ L := by
    nlinarith [Real.sq_sqrt (by linarith : 0 ≤ L), sq_nonneg (Real.sqrt L - 1)]
  exact (hJtwo.trans hs).trans hsqrtLe

theorem mrEventually_lastBlock_index_error {delta : ℝ} (hdelta : 0 < delta) :
    ∀ᶠ X : ℕ in atTop, 2 ≤ X ∧ 1 ≤ Real.log (X : ℝ) ∧
      ∀ {q : ℝ}, 1 ≤ q → ∀ {J : ℕ}, 1 ≤ J →
        mrLogScheduleUpper q J ≤ Real.sqrt (Real.log (X : ℝ)) →
        (J : ℝ) / X ≤ delta := by
  have hlim := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
    tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop 2,
    EulerSubpower.tendsto_log_nat_atTop.eventually (eventually_ge_atTop 1),
    hlim.eventually (gt_mem_nhds hdelta)] with X hX hlog hsmall
  refine ⟨hX, hlog, ?_⟩
  intro q hq J hJ hupper
  exact (div_le_div_of_nonneg_right (mrLastBlock_index_le_log hq hlog hJ hupper)
    (Nat.cast_nonneg X)).trans hsmall.le

end

end Erdos67b
