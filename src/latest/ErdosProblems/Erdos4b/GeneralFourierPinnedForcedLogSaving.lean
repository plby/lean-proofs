/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierPinnedForcedDistribution
import ErdosProblems.Erdos4b.GeneralFourierPinnedTauDecay

/-!
# Unconditional logarithmic saving for the aggregate forced-prime error

The extra forced-prime coordinate enlarges the divisor-power envelope,
but the proved prime-distribution theorem supplies every fixed logarithmic
saving. The constants are uniform in the pin and the Fourier cutoff.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

theorem exists_uniform_pinnedSourceForcedEndpoint_logSaving
    {K : ℕ} {J : Type*} (S : Finset J) (F : J → Fin K → ℝ → ℝ) (G : ℝ → ℝ)
    (hFcompact : ∀ j i, HasCompactSupport (F j i)) (hFcont : ∀ j i, Continuous (F j i))
    (hGcompact : HasCompactSupport G) (hGcont : Continuous G)
    (hFsupport : ∀ j ∈ S, ∀ u : Fin K → ℝ,
      (∀ i, 0 ≤ u i) → (∀ i, F j i (u i) ≠ 0) → (∑ i, u i) ≤ (1 : ℝ) / 10)
    (hGsupport : ∀ t, 0 ≤ t → G t ≠ 0 → t ≤ 1) (L : ℕ) :
    ∃ C ≥ 0, ∃ X₀ : ℕ, 3 ≤ X₀ ∧
      ∀ (h : Fin K) (P : Finset ℕ) (V : ℝ) (Y x : ℕ),
        (∀ p ∈ P, p.Prime) → 160 ≤ V → 1 < Y → (K : ℝ) * Real.log Y ≤ V / 40 →
        3 * V / 4 ≤ Real.log x → X₀ ≤ x →
        pinnedSourceForcedEndpointErrorBound S F G h P Y x V (Real.log Y) ≤
          C * (x : ℝ) / Real.log x ^ L := by
  let D : ℕ := (2 ^ (4 * K)) ^ 2
  have he : 0 < ((2 * (D + L) : ℕ) : ℝ) := by
    dsimp only [D]
    positivity
  obtain ⟨C₀, hC₀, hcoef⟩ := exists_uniform_pinnedSourceFlatCoefficient_bound
    S F G hFcompact hFcont hGcompact hGcont
  obtain ⟨C, X₀, hw⟩ := exists_pinnedTwoFifthsPrimeLevelWitness he
  refine ⟨C₀ ^ 2 * (Real.sqrt (6 * C) * 2 ^ D), by positivity, X₀, hw.2.1, ?_⟩
  intro h P V Y x hP hV hY hsmall hlog hx
  have hxpos : 0 < x := lt_of_lt_of_le (lt_of_lt_of_le (by norm_num : 0 < 3) hw.2.1) hx
  have hlog1 : 1 ≤ Real.log x := by linarith
  have hRpos : 1 ≤ pinnedSourceForcedProductRadius K V Y :=
    pinnedSourceForcedProductRadius_pos K V (by omega)
  have hRx := pinnedSourceForcedProductRadius_le_endpoint h.pos hV (by omega) hsmall hxpos hlog
  have hdecay := pinnedFlatTauDiscrepancyBound_le_logSaving (K + 1) L hw.1
    hxpos hlog1 hRpos hRx
  simp only [Nat.add_sub_cancel] at hdecay
  calc
    _ ≤ C₀ ^ 2 * pinnedFlatTauDiscrepancyBound (K + 1) C
        ((2 * (D + L) : ℕ) : ℝ) x (pinnedSourceForcedProductRadius K V Y) :=
      primeLevelWitness_pinnedSourceForcedEndpointErrorBound_le S F G h P hP hV hY
        hsmall hxpos hlog hFsupport hGsupport hC₀ (hcoef h V (Real.log Y)) hw hx
    _ ≤ C₀ ^ 2 * (Real.sqrt (6 * C) * 2 ^ D * (x : ℝ) / Real.log x ^ L) :=
      mul_le_mul_of_nonneg_left hdecay (sq_nonneg C₀)
    _ = _ := by ring

end

end Erdos4b
