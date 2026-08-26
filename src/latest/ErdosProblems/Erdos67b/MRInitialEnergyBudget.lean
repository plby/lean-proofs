import ErdosProblems.Erdos67b.MRClassSummation

/-! # The initial first-small energy cost and its exponential decay -/

open Filter
open scoped Topology

namespace Erdos67b

noncomputable section

def mrFirstSmallInitialCost : ℝ := (4096 * Real.exp 1 + 3072) * (1 + Real.pi)

def mrFirstSmallTailCost : ℝ := (16384 * Real.exp 13 + 512) * (1 + Real.pi)

def mrFirstSmallInitialEnvelope (eta p q : ℝ) : ℝ :=
  mrFirstSmallInitialCost * Real.exp (Real.log q / 3 - (1 / 6 - eta) * p) +
    mrFirstSmallTailCost * Real.exp (-p)

theorem mrFirstResolution_inv_eq (eta p q : ℝ) :
    1 / mrLogBlockResolution eta p q 1 =
      Real.exp (Real.log q / 3 - (1 / 6 - eta) * p) := by
  simp only [mrLogBlockResolution, one_pow, one_mul, one_div, ← Real.exp_neg]
  congr 1
  ring

theorem mrFirstSmallInitialEnvelope_nonneg (eta p q : ℝ) :
    0 ≤ mrFirstSmallInitialEnvelope eta p q := by
  unfold mrFirstSmallInitialEnvelope mrFirstSmallInitialCost mrFirstSmallTailCost
  positivity

theorem mrFirstSmallEnergyBudget_le_initialEnvelope
    {eta p q T : ℝ} (hq : 0 ≤ q) {X : ℕ} (hX : 0 < X) (J : ℕ)
    (_hT : 0 ≤ T) (hTX : T ≤ (X : ℝ) * Real.exp (-q)) :
    mrFirstSmallEnergyBudget eta p q X J T ≤
      mrFirstSmallInitialEnvelope eta p q + 256 * (1 + Real.pi) * (J : ℝ) / X := by
  have hXr : (0 : ℝ) < X := by exact_mod_cast hX
  have hquot : T / X ≤ Real.exp (-q) := (div_le_iff₀ hXr).2 (by nlinarith)
  have htime : T / X + 1 ≤ 2 := by
    have he := Real.exp_le_one_iff.mpr (by linarith : -q ≤ 0)
    linarith
  have hfirst : T / X * Real.exp q + 1 ≤ 2 := by
    have hh := mul_le_mul_of_nonneg_right hquot (Real.exp_pos q).le
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at hh
    linarith
  have hres : 12 / mrLogBlockResolution eta p q 1 =
      12 * Real.exp (Real.log q / 3 - (1 / 6 - eta) * p) := by
    rw [show 12 / mrLogBlockResolution eta p q 1 =
      12 * (1 / mrLogBlockResolution eta p q 1) by ring, mrFirstResolution_inv_eq]
  unfold mrFirstSmallEnergyBudget
  rw [hres]
  calc
    _ ≤ 2048 * Real.exp 1 * (1 + Real.pi) * 2 *
        Real.exp (Real.log q / 3 - (1 / 6 - eta) * p) +
        8192 * Real.exp 13 * (1 + Real.pi) * 2 * Real.exp (-p) +
        128 * (1 + Real.pi) * 2 *
          (12 * Real.exp (Real.log q / 3 - (1 / 6 - eta) * p) +
            (J : ℝ) / X + 2 * Real.exp (-p)) := by gcongr
    _ = _ := by
      unfold mrFirstSmallInitialEnvelope mrFirstSmallInitialCost mrFirstSmallTailCost
      ring

theorem mrTendsto_firstSmallInitialEnvelope {eta rho : ℝ}
    (heta : eta ≤ 1 / 12) (hrho : 0 < rho) :
    Tendsto (fun q : ℝ ↦ mrFirstSmallInitialEnvelope eta (rho * q) q) atTop (𝓝 0) := by
  have ha : 0 < (1 / 6 - eta) * rho := mul_pos (by linarith) hrho
  have hbeta : Tendsto
      (fun q : ℝ ↦ Real.exp (Real.log q / 3 - (1 / 6 - eta) * (rho * q))) atTop (𝓝 0) := by
    apply (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
      (1 / 3) ((1 / 6 - eta) * rho) ha).congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with q hq
    rw [Real.rpow_def_of_pos hq, ← Real.exp_add]
    congr 1
    ring
  have htail := Real.tendsto_exp_neg_atTop_nhds_zero.comp
    (tendsto_id.const_mul_atTop hrho)
  have hh := (hbeta.const_mul mrFirstSmallInitialCost).add
    (htail.const_mul mrFirstSmallTailCost)
  simpa only [Function.comp_apply, id_eq, mrFirstSmallInitialEnvelope, mul_zero, zero_add] using hh

end

end Erdos67b
