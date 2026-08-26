/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierPinnedDistributionRange
import BoundedGaps.BombieriVinogradov.Proof.MainTheorem

/-!
# Unconditional prime-distribution input for the pinned source endpoint

The level witness is obtained from the bundled proved
Bombieri--Vinogradov theorem, not supplied as an analytic assumption.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

theorem exists_pinnedTwoFifthsPrimeLevelWitness {exponent : ℝ} (he : 0 < exponent) :
    ∃ C : ℝ, ∃ X₀ : ℕ, BoundedGaps.Maynard.PrimeLevelWitness (2 / 5) exponent C X₀ := by
  apply BoundedGaps.Maynard.hasPrimeLevel_exists_witness _ he
  exact BoundedGaps.Maynard.unconditional_bombieriVinogradov (2 / 5) (by norm_num) (by norm_num)

theorem exists_uniform_pinnedSourceEndpointErrorBound
    {K : ℕ} {J : Type*} (S : Finset J) (F : J → Fin K → ℝ → ℝ) (G : ℝ → ℝ)
    (hFcompact : ∀ j i, HasCompactSupport (F j i)) (hFcont : ∀ j i, Continuous (F j i))
    (hGcompact : HasCompactSupport G) (hGcont : Continuous G)
    (hFsupport : ∀ j ∈ S, ∀ u : Fin K → ℝ,
      (∀ i, 0 ≤ u i) → (∀ i, F j i (u i) ≠ 0) → (∑ i, u i) ≤ (1 : ℝ) / 10)
    (hGsupport : ∀ t, 0 ≤ t → G t ≠ 0 → t ≤ 1)
    {exponent : ℝ} (he : 0 < exponent) :
    ∃ C₀ ≥ 0, ∃ C ≥ 0, ∃ X₀ : ℕ, 3 ≤ X₀ ∧
      ∀ (h : Fin K) (P : Finset ℕ) (V LE : ℝ) (x : ℕ),
        (∀ p ∈ P, p.Prime) → 80 ≤ V → 0 < LE → (K : ℝ) * LE ≤ V / 40 →
        3 * V / 4 ≤ Real.log x → X₀ ≤ x →
        pinnedSourceEndpointErrorBound S F G h P x V LE ≤
          C₀ ^ 2 * pinnedFlatTauDiscrepancyBound K C exponent x
            (pinnedSourceProductRadius K V LE) := by
  obtain ⟨C₀, hC₀, hcoef⟩ := exists_uniform_pinnedSourceFlatCoefficient_bound S F G
    hFcompact hFcont hGcompact hGcont
  obtain ⟨C, X₀, hw⟩ := exists_pinnedTwoFifthsPrimeLevelWitness he
  refine ⟨C₀, hC₀, C, hw.1, X₀, hw.2.1, ?_⟩
  intro h P V LE x hP hV hLE hsmall hlog hx
  have hxpos : 0 < x := lt_of_lt_of_le (lt_of_lt_of_le (by norm_num : 0 < 3) hw.2.1) hx
  exact primeLevelWitness_pinnedSourceEndpointErrorBound_le_twoFifths S F G h P hP
    hV hLE hsmall hxpos hlog hFsupport hGsupport hC₀ (hcoef h V LE) hw hx

end

end Erdos4b
