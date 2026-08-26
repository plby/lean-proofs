import ErdosProblems.Erdos1148.RefinedLocalCover
import ErdosProblems.Erdos1148.UnconditionalForwardPairBound
import ErdosProblems.Erdos1148.FiniteCoverPairMass

/-! # Unconditional packet mass bounds for many cusp visits with fixed-height endpoints -/

namespace Erdos1148.DukeArithmetic

open MeasureTheory
open scoped MatrixGroups

theorem exists_unconditional_packet_high_cusp_visit_mass_bound {η ε σ : ℝ}
    (hηpos : 0 < η) (hη : η ≤ 1 / 192) (hε : 0 < ε) (hσ : 0 < σ) :
    ∃ H₀ : ℝ, 1 < H₀ ∧ ∀ H : ℝ, H₀ ≤ H → ∃ C : ℝ, 0 < C ∧
      ∀ (d : ℕ) (hd : 0 < (d : ℤ)) (hns : ¬IsSquare (d : ℤ)), IntegralDiscrForm d →
      ∀ (n : ℕ) (E : Set SL(2, ℝ)) (A : ℝ), LiftForwardClose η 0 E →
        (normalizedDiscriminantPacket hd hns).real
          (modularMk '' highCuspVisitsWithBoundedEndpoints H n A E) ^ 2 ≤
          C * Real.exp ((1 + ε) * n - A / 2) *
            ((d : ℝ) ^ (-1 / 2 + σ) + (d : ℝ) ^ σ * Real.exp (-(n : ℝ))) := by
  obtain ⟨H₀, hH₀, hcover⟩ := exists_refined_local_cusp_cover hηpos (by linarith) hε
  obtain ⟨K, hK, hcollision⟩ := exists_unconditional_normalizedPacket_forwardPairs_bound hσ
  refine ⟨H₀, hH₀, ?_⟩
  intro H hH
  obtain ⟨C, hC, hboxes⟩ := hcover H hH
  refine ⟨C * K, mul_pos hC hK, ?_⟩
  intro d hd hns base n E A hE
  let μ := normalizedDiscriminantPacket hd hns
  let : IsProbabilityMeasure μ := normalizedDiscriminantPacket_isProbability hd hns base
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hH1 : 1 < H := hH₀.trans_le hH
  have hlog : 0 ≤ Real.log H := (Real.log_pos hH1).le
  let T := (n : ℝ) + 4 * Real.log H
  have hT : 0 ≤ T := by dsimp only [T]; positivity
  have hr : 0 < 32 * η := by positivity
  have hrmax : 32 * η ≤ 1 / 6 := by linarith
  have hpair₀ := hcollision d hd hns base (32 * η) T hr hrmax hT
  have hsq : (32 * η) ^ 2 ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ hr.le (by linarith : 32 * η ≤ 1) 2
  have hexp : Real.exp (-T) ≤ Real.exp (-(n : ℝ)) :=
    Real.exp_le_exp.mpr (by dsimp only [T]; linarith)
  have hfactor : (32 * η) ^ 2 * Real.exp (-T) ≤ Real.exp (-(n : ℝ)) := by
    simpa only [one_mul] using mul_le_mul hsq hexp (Real.exp_pos _).le (by norm_num : (0 : ℝ) ≤ 1)
  have hpair : (μ.prod μ).real (modularForwardBowenPairs (32 * η) T) ≤
      K * ((d : ℝ) ^ (-1 / 2 + σ) + (d : ℝ) ^ σ * Real.exp (-(n : ℝ))) := by
    apply hpair₀.trans
    apply mul_le_mul_of_nonneg_left _ hK.le
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hfactor (Real.rpow_nonneg hdR.le σ))
  obtain ⟨N, B, hN, _, hmeas, hcov, hB⟩ := hboxes n E A hE
  have hmass := finite_cover_mass_sq_le_pair_mass μ B hmeas hcov hB
  calc
    _ ≤ (N : ℝ) * (μ.prod μ).real (modularForwardBowenPairs (32 * η) T) := hmass
    _ ≤ (C * Real.exp ((1 + ε) * n - A / 2)) *
        (K * ((d : ℝ) ^ (-1 / 2 + σ) + (d : ℝ) ^ σ * Real.exp (-(n : ℝ)))) :=
      mul_le_mul hN hpair measureReal_nonneg (by positivity)
    _ = _ := by ring

end Erdos1148.DukeArithmetic
