import ErdosProblems.Erdos1148.UnconditionalForwardPairBound

/-! # A convenient collision bound when the forward duration exceeds the counting window -/

namespace Erdos1148.DukeArithmetic

open MeasureTheory

theorem exists_unconditional_forwardPairs_time_bound {σ : ℝ} (hσ : 0 < σ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (d : ℕ) (hd : 0 < (d : ℤ)) (hns : ¬IsSquare (d : ℤ)),
      IntegralDiscrForm d → ∀ (r s T : ℝ), 0 < r → r ≤ 1 / 6 → 0 ≤ T → s ≤ T →
        ((normalizedDiscriminantPacket hd hns).prod
          (normalizedDiscriminantPacket hd hns)).real (modularForwardBowenPairs r T) ≤
            K * ((d : ℝ) ^ (-1 / 2 + σ) + (d : ℝ) ^ σ * Real.exp (-s)) := by
  obtain ⟨K, hK, hpair⟩ := exists_unconditional_normalizedPacket_forwardPairs_bound hσ
  refine ⟨K, hK, ?_⟩
  intro d hd hns base r s T hr hrmax hT hsT
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hsq : r ^ 2 ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ hr.le (by linarith : r ≤ 1) 2
  have hexp : Real.exp (-T) ≤ Real.exp (-s) := Real.exp_le_exp.mpr (by linarith)
  have hfactor : r ^ 2 * Real.exp (-T) ≤ Real.exp (-s) := by
    simpa only [one_mul] using mul_le_mul hsq hexp (Real.exp_pos _).le (by norm_num : (0 : ℝ) ≤ 1)
  apply (hpair d hd hns base r T hr hrmax hT).trans
  exact mul_le_mul_of_nonneg_left
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left hfactor (Real.rpow_nonneg hdR.le σ))) hK.le

end Erdos1148.DukeArithmetic
