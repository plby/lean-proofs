import ErdosProblems.Erdos1148.RefinedGlobalCover
import ErdosProblems.Erdos1148.ForwardPairTimeBound
import ErdosProblems.Erdos1148.FiniteCoverPairMass
import ErdosProblems.Erdos1148.ModularFlowHomeomorph

/-! # An unconditional global packet estimate for high-cusp visit counts -/

namespace Erdos1148.DukeArithmetic

open MeasureTheory

theorem exists_unconditional_packet_global_high_cusp_mass_bound {η ε σ : ℝ}
    (hηpos : 0 < η) (hη : η ≤ 1 / 192) (hε : 0 < ε) (hσ : 0 < σ) :
    ∃ H₀ : ℝ, 1 < H₀ ∧ ∀ H : ℝ, H₀ ≤ H → ∃ C : ℝ, 0 < C ∧
      ∀ Y : ℝ, 1 ≤ Y → ∀ (d : ℕ) (hd : 0 < (d : ℤ)) (hns : ¬IsSquare (d : ℤ)),
      IntegralDiscrForm d → ∀ (n : ℕ) (A : ℝ),
        (normalizedDiscriminantPacket hd hns).real (modularHighCuspVisits H Y n A) ^ 2 ≤
          C * (Y + 1) ^ 11 * Real.exp ((1 + ε) * n - A / 2) *
            ((d : ℝ) ^ (-1 / 2 + σ) + (d : ℝ) ^ σ * Real.exp (-(n : ℝ))) := by
  obtain ⟨H₀, hH₀, hcover⟩ := exists_refined_global_cusp_cover hηpos (by linarith) hε
  obtain ⟨K, hK, hcollision⟩ := exists_unconditional_forwardPairs_time_bound hσ
  refine ⟨H₀, hH₀, ?_⟩
  intro H hH
  obtain ⟨C, hC, hboxes⟩ := hcover H hH
  refine ⟨C * K, mul_pos hC hK, ?_⟩
  intro Y hY d hd hns base n A
  let μ := normalizedDiscriminantPacket hd hns
  let : IsProbabilityMeasure μ := normalizedDiscriminantPacket_isProbability hd hns base
  have hlog : 0 ≤ Real.log H := (Real.log_pos (hH₀.trans_le hH)).le
  let T := (n : ℝ) + 4 * Real.log H
  have hT : 0 ≤ T := by dsimp only [T]; positivity
  have hnT : (n : ℝ) ≤ T := by dsimp only [T]; linarith
  have hpair := hcollision d hd hns base (32 * η) (n : ℝ) T
    (by positivity) (by linarith) hT hnT
  obtain ⟨N, B, hN, _, hmeas, hcov, hB⟩ := hboxes Y hY n A
  have hmass := finite_cover_mass_sq_le_pair_mass μ B hmeas hcov hB
  have hbuffer : μ.real (modularBufferedHighCuspVisits H Y n A) =
      μ.real (modularHighCuspVisits H Y n A) :=
    modular_flow_measureReal_preimage μ (normalizedDiscriminantPacket_flow_invariant hd hns)
      (2 * Real.log H) _
  rw [hbuffer] at hmass
  calc
    _ ≤ (N : ℝ) * (μ.prod μ).real (modularForwardBowenPairs (32 * η) T) := hmass
    _ ≤ (C * (Y + 1) ^ 11 * Real.exp ((1 + ε) * n - A / 2)) *
        (K * ((d : ℝ) ^ (-1 / 2 + σ) + (d : ℝ) ^ σ * Real.exp (-(n : ℝ)))) :=
      mul_le_mul hN hpair measureReal_nonneg (by positivity)
    _ = _ := by ring

end Erdos1148.DukeArithmetic
