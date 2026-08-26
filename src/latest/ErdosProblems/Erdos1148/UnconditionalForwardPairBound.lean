import ErdosProblems.Erdos1148.UnconditionalBowenPairBound
import ErdosProblems.Erdos1148.ModularForwardBowenPairs

/-! # Unconditional collision bounds for forward orbit segments -/

namespace Erdos1148.DukeArithmetic

open MeasureTheory

theorem exists_unconditional_normalizedPacket_forwardPairs_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ (d : ℕ) (hd : 0 < (d : ℤ)) (hns : ¬IsSquare (d : ℤ)),
      IntegralDiscrForm d → ∀ (r T : ℝ), 0 < r → r ≤ 1 / 6 → 0 ≤ T →
        ((normalizedDiscriminantPacket hd hns).prod
          (normalizedDiscriminantPacket hd hns)).real (modularForwardBowenPairs r T) ≤
            K * ((d : ℝ) ^ (-1 / 2 + ε) + (d : ℝ) ^ ε * (r ^ 2 * Real.exp (-T))) := by
  obtain ⟨K, hK, hbound⟩ := exists_unconditional_normalizedPacket_bowenPairs_bound hε
  refine ⟨K, hK, ?_⟩
  intro d hd hns base r T hr hrsix hT
  let μ := normalizedDiscriminantPacket hd hns
  let : IsProbabilityMeasure μ := normalizedDiscriminantPacket_isProbability hd hns base
  have hδ : r * Real.exp (-(T / 2)) ≤ 1 / 6 := by
    have hExp : Real.exp (-(T / 2)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    exact (mul_le_of_le_one_right hr.le hExp).trans hrsix
  have h := hbound d hd hns base r (r * Real.exp (-(T / 2))) hr.le (by linarith)
    (mul_pos hr (Real.exp_pos _)) hδ
  have hmass : (μ.prod μ).real (modularForwardBowenPairs r T) =
      (μ.prod μ).real (modularBowenPairs r (r * Real.exp (-(T / 2)))) :=
    congrArg ENNReal.toReal (modularForwardBowenPairs_mass μ
      (normalizedDiscriminantPacket_flow_invariant hd hns) r T)
  rw [hmass]
  have hexp : Real.exp (-(T / 2)) ^ 2 = Real.exp (-T) := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num <;> ring
  simpa only [mul_pow, hexp] using h

end Erdos1148.DukeArithmetic
