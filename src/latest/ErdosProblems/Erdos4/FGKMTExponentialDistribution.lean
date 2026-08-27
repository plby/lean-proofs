import ErdosProblems.Erdos4.FGKMTExponentialEnvelope
import ErdosProblems.Erdos4.FGKMTDistributionCutoffs

/-!
# Exponential averaged distribution after prime excision

This is an unconditional estimate at every sufficiently large natural
endpoint, with modulus level the cube root of the endpoint. All constants
are chosen before the endpoint and its omitted prime.
-/

namespace Erdos4.FGKMT

open Filter BoundedGaps.Maynard

theorem exists_exponential_centered_distribution :
    ∃ a C : ℝ, 0 < a ∧ a ≤ 1 / 4 ∧ 0 < C ∧
      ∀ᶠ x : ℕ in atTop, ∃ B : ℕ,
        B ≤ exponentialConductorCutoff a x ∧ (B = 1 ∨ B.Prime) ∧
          excisedCenteredSum x (powerDistributionLevel x) B ≤
            C * ((x : ℝ) * Real.exp (-(a / 2) * Real.sqrt (Real.log (x : ℝ)))) := by
  obtain ⟨C₀, c, hC₀, hc, X₀, _hX₀, hfinite⟩ := exists_excised_distribution_envelope
  let L : ℝ := 5 * vaughanPrimitiveMeanEquationOneOneConstant (Real.log 4 + 4)
  let a : ℝ := min (c / 4) (1 / 4)
  let C : ℝ := 4 + 4 * C₀ + 62 * L
  have hL : 0 ≤ L := mul_nonneg (by norm_num)
    (vaughanPrimitiveMeanEquationOneOneConstant_nonneg _)
  have ha : 0 < a := lt_min (by positivity) (by norm_num)
  have ha1 : a ≤ 1 / 4 := min_le_right _ _
  have hca : 4 * a ≤ c := by
    have hh : a ≤ c / 4 := min_le_left _ _
    linarith
  have hC : 0 < C := by unfold C; positivity
  refine ⟨a, C, ha, ha1, hC, ?_⟩
  have hcut := eventually_distribution_cutoffs ha ha1
  have hdecay := eventually_averagedErrorEnvelope_decay hC₀.le hL ha hca
  filter_upwards [hcut, hdecay, eventually_ge_atTop X₀] with x hcut hdecay hx
  obtain ⟨_hx1, hR2, hRQ, hQsqrt, hRheight, hRlo, hRhi, hQcube⟩ := hcut
  obtain ⟨B, hBR, hB, hbound⟩ := hfinite (exponentialConductorCutoff a x) hR2
  refine ⟨B, hBR, hB, ?_⟩
  have hh := hbound x (powerDistributionLevel x) hx hRQ hQsqrt hRheight
  change excisedCenteredSum x (powerDistributionLevel x) B ≤
    averagedErrorEnvelope C₀ c L x (powerDistributionLevel x) (exponentialConductorCutoff a x) at hh
  exact hh.trans (hdecay (exponentialConductorCutoff a x) (powerDistributionLevel x)
    (by omega) hRQ hQcube hRlo hRhi)

end Erdos4.FGKMT
