import ErdosProblems.Erdos67b.MRInitialEnergyBudget
import ErdosProblems.Erdos67b.MRPrimeBlockMass

/-! # Feasible original schedules with small first-small energy cost -/

open Filter

namespace Erdos67b

noncomputable section

theorem mrLogGap_of_ratio {rho q G : ℝ} (hrho : 0 < rho) (hq : 0 < q)
    (hrhoG : rho ≤ Real.exp (-G)) : G ≤ Real.log q - Real.log (rho * q) := by
  have hh := Real.log_le_log hrho hrhoG
  rw [Real.log_exp] at hh
  rw [Real.log_mul hrho.ne' hq.ne']
  linarith

theorem mrExists_initial_small_energy {eta rhoMax epsilon : ℝ}
    (heta0 : 0 < eta) (heta1 : eta ≤ 1 / 12)
    (hrhoMax : 0 < rhoMax) (hepsilon : 0 < epsilon) (Q : ℝ) :
    ∃ p q : ℝ, Q ≤ q ∧ Real.exp 1 ≤ q ∧ 2 ≤ p ∧ 2 * p ≤ q ∧ p / q ≤ rhoMax ∧
      1 ≤ Real.log q ∧ 4096 * Real.log q ≤ eta * p ∧
      Real.log 2 + 2 * PrimeEstimates.mertensBound ≤ Real.log q - Real.log p ∧
      mrFirstSmallInitialEnvelope eta p q ≤ epsilon := by
  let G := Real.log 2 + 2 * PrimeEstimates.mertensBound
  let ceiling := min rhoMax (min (1 / 2 : ℝ) (Real.exp (-G)))
  have hceiling : 0 < ceiling := lt_min hrhoMax (lt_min (by norm_num) (Real.exp_pos _))
  obtain ⟨rho, hrho, hrhoCeil, _, hsource⟩ :=
    exists_eventually_mrLogSchedule_initial heta0 hceiling
  have hrhoMax' : rho ≤ rhoMax := hrhoCeil.trans (min_le_left _ _)
  have hrhoHalf : rho ≤ 1 / 2 := hrhoCeil.trans
    ((min_le_right _ _).trans (min_le_left _ _))
  have hrhoG : rho ≤ Real.exp (-G) := hrhoCeil.trans
    ((min_le_right _ _).trans (min_le_right _ _))
  have hsmall := (mrTendsto_firstSmallInitialEnvelope heta1 hrho).eventually
    (gt_mem_nhds hepsilon)
  obtain ⟨q, hq, hcost, hQ⟩ := (hsource.and (hsmall.and (eventually_ge_atTop Q))).exists
  have hqpos : 0 < q := (Real.exp_pos 1).trans_le hq.1
  have hlogq : 1 ≤ Real.log q := by
    have hh := Real.log_le_log (Real.exp_pos 1) hq.1
    simpa only [Real.log_exp] using hh
  refine ⟨rho * q, q, hQ, hq.1, hq.2.1, ?_, ?_, hlogq, hq.2.2.2,
    mrLogGap_of_ratio hrho hqpos hrhoG, hcost.le⟩
  · nlinarith [mul_le_mul_of_nonneg_right hrhoHalf hqpos.le]
  · simpa only [mul_div_cancel_right₀ _ hqpos.ne'] using hrhoMax'

end

end Erdos67b
