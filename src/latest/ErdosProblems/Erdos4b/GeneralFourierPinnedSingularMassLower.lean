/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierPinnedCombinedProduct
import ErdosProblems.Erdos4b.GeneralFourierPinnedWeightedLower
import ErdosProblems.Erdos4b.SingularGenericBounds

/-!
# Lower bound for the literal singular-weighted pinned prime mass

The inverse-singular weight lower bound is converted into a bound for
the actual sum of squares divided by the unpinned singular series.
The residual cofactor product is retained for the later fibre cancellation.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

theorem singularWeightedMass_lower_of_normalized_lower
    {scale series fixed universal count mass residual c : ℝ}
    (hscale : 0 < scale) (hseries : 0 < series) (hfixed : 0 < fixed)
    (huniversal : 0 < universal) (hcount : 0 < count) (hc : 0 ≤ c)
    (hratio : (1 / 2 : ℝ) * residual ≤ series * fixed / universal)
    (hweight : c ≤ scale / (series * count) * universal / fixed * mass) :
    c * residual * count / (2 * scale) ≤ mass := by
  calc
    _ = (c * count / scale) * ((1 / 2 : ℝ) * residual) := by ring
    _ ≤ (c * count / scale) * (series * fixed / universal) :=
      mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = (series * fixed * count / (universal * scale)) * c := by ring
    _ ≤ (series * fixed * count / (universal * scale)) *
        (scale / (series * count) * universal / fixed * mass) :=
      mul_le_mul_of_nonneg_left hweight (by positivity)
    _ = mass := by field_simp

theorem pinnedSingularWeightedPrimeMass_lower
    {K w m p₀ Y X A B N : ℕ} {I : Type*}
    (S : Finset I) (F : I → Fin K → ℝ → ℝ) (G : ℝ → ℝ) (h : Fin K)
    (hfour : 4 * K ≤ w) (hm : 0 < m) (hmeven : Even m) (hp₀ : p₀.Prime)
    (hwy : w ≤ Y) (hYp₀ : Y < p₀) (hcop : (m * p₀ - 1).Coprime (primorial Y))
    (hX : 1 < X) (hY : 1 < Y) (hcount : 0 < (auxiliaryPrimeInterval A B).card)
    {c : ℝ} (hc : 0 ≤ c)
    (hweight : c ≤ sourcePinnedInverseSingularNormalizedWeight S F G h w m p₀ Y X A B N) :
    c * residualCofactorLocalProduct Y m * (auxiliaryPrimeInterval A B).card /
        (2 * (Real.log X ^ (K - 1) * Real.log Y ^ (K - 1))) ≤
      ∑ q ∈ auxiliaryPrimeInterval A B,
        pinnedSourceRealIntegerWeight S F G h
          (selectedFourierPrimeCutoff (fun p ↦ decide (w < p)) (boundedFourierPrimes N))
          w m p₀ q (Real.log X) (Real.log Y) /
            largeGapSingularSeries (preSievedShifts K w) m q Y := by
  have hw : 0 < w := by have := h.pos; omega
  have hKw : K ≤ w := by omega
  have hlarge : 2 * Fintype.card (PinnedShiftIndex h) ≤ w := by
    rw [card_pinnedShiftIndex]
    omega
  have hSS := pinnedSingularSeries_pos h hm hp₀ hYp₀ hKw hlarge hcop
  have hfixed := fixedSingularInverseFactor_pos (y := Y) (m := m) hfour hw
  have hsmall := largeGapSingularSeries_preSievedShifts_pos (K := K) (m := m) (q := 1) (y := w)
    (by omega : 2 * K ≤ w) hmeven
  have hgeneric := genericRoughSingularProduct_pos (y := Y) hfour
  have hscale : 0 < Real.log X ^ (K - 1) * Real.log Y ^ (K - 1) :=
    mul_pos (pow_pos (Real.log_pos (by exact_mod_cast hX)) _)
      (pow_pos (Real.log_pos (by exact_mod_cast hY)) _)
  rw [sourcePinnedInverseSingularNormalizedWeight_eq_singularQuotient S F G h hfour hwy hmeven]
    at hweight
  exact singularWeightedMass_lower_of_normalized_lower hscale hSS hfixed (mul_pos hsmall hgeneric)
    (by exact_mod_cast hcount) hc
    (half_residualCofactorLocalProduct_le_pinnedCombinedSingularRatio
      h hfour hm hmeven hp₀ hwy hYp₀ hcop) hweight

end

end Erdos4b
