import ErdosProblems.Erdos1148.ModularBowenPairs
import ErdosProblems.Erdos1148.UnconditionalPairBound

/-! # Unconditional collision bounds for long diagonal-flow tubes -/

namespace Erdos1148.DukeArithmetic

open MeasureTheory

theorem exists_unconditional_normalizedPacket_bowenPairs_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ (d : ℕ) (hd : 0 < (d : ℤ)) (hns : ¬IsSquare (d : ℤ)),
      IntegralDiscrForm d → ∀ (r δ : ℝ), 0 ≤ r → r ≤ 1 / 2 → 0 < δ → δ ≤ 1 / 6 →
        ((normalizedDiscriminantPacket hd hns).prod
          (normalizedDiscriminantPacket hd hns)).real (modularBowenPairs r δ) ≤
            K * ((d : ℝ) ^ (-1 / 2 + ε) + (d : ℝ) ^ ε * δ ^ 2) := by
  obtain ⟨C, hC, hpair⟩ := exists_unconditional_normalizedPacketProduct_close_le hε
  refine ⟨60 * C, by positivity, ?_⟩
  intro d hd hns base r δ hr hrhalf hδ hδsixth
  let μ := normalizedDiscriminantPacket hd hns
  let : IsProbabilityMeasure μ := normalizedDiscriminantPacket_isProbability hd hns base
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hpairReal : (μ.prod μ).real (modularClosePairs (3 * δ)) ≤
      C * ((d : ℝ) ^ (-1 / 2 + ε) * (3 * δ) + (d : ℝ) ^ ε * (3 * δ) ^ 3) := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hpair d hd hns base (3 * δ)
      (by positivity) (by linarith))
    change (μ.prod μ).real (modularClosePairs (3 * δ)) ≤
      (ENNReal.ofReal (C * ((d : ℝ) ^ (-1 / 2 + ε) * (3 * δ) +
        (d : ℝ) ^ ε * (3 * δ) ^ 3))).toReal at h
    rwa [ENNReal.toReal_ofReal (by positivity)] at h
  have htube := modularBowenPairs_mass_le_closePairs μ
    (normalizedDiscriminantPacket_flow_invariant hd hns) hr hrhalf hδ (by linarith)
  refine htube.trans ((mul_le_mul_of_nonneg_left hpairReal (by positivity)).trans ?_)
  have heq : (2 / δ) * (C * ((d : ℝ) ^ (-1 / 2 + ε) * (3 * δ) +
      (d : ℝ) ^ ε * (3 * δ) ^ 3)) =
        6 * C * (d : ℝ) ^ (-1 / 2 + ε) + 54 * C * ((d : ℝ) ^ ε * δ ^ 2) := by
    field_simp
    <;> ring
  rw [heq]
  have hfirst : 0 ≤ C * (d : ℝ) ^ (-1 / 2 + ε) := by positivity
  have hsecond : 0 ≤ C * ((d : ℝ) ^ ε * δ ^ 2) := by positivity
  nlinarith

end Erdos1148.DukeArithmetic
