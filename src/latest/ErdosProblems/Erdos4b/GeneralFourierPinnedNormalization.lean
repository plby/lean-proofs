/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierPinnedSingularProduct

/-!
# Finite pinned singular-series normalization

The small-prime density is one for the pinned forms. The full Fourier
normalization times the generic tail is exactly the reciprocal of the
literal finite pinned singular series times the logarithmic scales.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

theorem pinnedSingularSeries_preSieveCutoff_eq_inverse
    {K w m p₀ Y : ℕ} (h : Fin K) (hm : 0 < m) (hp₀ : p₀.Prime)
    (hwY : w ≤ Y) (hYp₀ : Y < p₀) (hcop : (m * p₀ - 1).Coprime (primorial Y)) :
    (pinnedSingularSeries h w m p₀ w : ℂ) =
      (smallDoubledFourierReferenceProduct (ι := PinnedShiftIndex h) w (fun _ _ ↦ 0))⁻¹ := by
  rw [pinnedSingularSeries, Complex.ofReal_prod, smallDoubledFourierReferenceProduct,
    ← Finset.prod_inv_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  have hpw := (mem_boundedFourierPrimes w p).mp hp
  have hmult : pinnedLocalMultiplicity h w m p₀ p = 0 := by
    rw [pinnedLocalMultiplicity, pinnedLocalForbiddenResidues_eq_empty_of_le_cutoff h p hpw
      (pinnedResidual_not_dvd_prime hp₀ hYp₀ p (hpw.trans hwY))
      (pinnedResidual_companion_numerator_ne_zero hm hp₀.pos hcop p (hpw.trans hwY)),
      Finset.card_empty]
  simp only [pinnedLocalFactor, hmult, Nat.cast_zero, zero_div, sub_zero, one_mul,
    Complex.ofReal_pow, Complex.ofReal_inv, Complex.ofReal_sub, Complex.ofReal_one,
    Complex.ofReal_div, Complex.ofReal_natCast, doubledFourierReferenceFactor_zero,
    inv_pow, Fintype.card_sum, two_mul]

theorem genericPinnedFourierSingularTail_ne_zero
    {K Y : ℕ} (h : Fin K)
    (hY : 7 * (Fintype.card (PinnedShiftIndex h ⊕ PinnedShiftIndex h) : ℝ) ≤ Y) :
    genericPinnedFourierSingularTail h Y ≠ 0 :=
  tprod_roughDoubledFourierSingularFactor_ne_zero (ι := PinnedShiftIndex h)
    (fun _ ↦ ∅) (fun _ ↦ true) (M := 1) (by norm_num) hY
    (fun p hp ↦ Nat.zero_le _) (fun p hp hn ↦ ⟨rfl, rfl⟩)

def pinnedFiniteFourierNormalization {K : ℕ} (h : Fin K) (w m p₀ Y : ℕ)
    (L : (PinnedShiftIndex h ⊕ PinnedShiftIndex h) → ℝ) : ℂ :=
  (∏ i, (L i : ℂ)) / (pinnedSingularSeries h w m p₀ Y : ℂ)

theorem pinnedFourierNormalization_mul_genericTail
    {K w m p₀ Y : ℕ} (h : Fin K) (hm : 0 < m) (hp₀ : p₀.Prime)
    (hw : 14 * K + 1 ≤ w) (hwY : w ≤ Y) (hYp₀ : Y < p₀)
    (hcop : (m * p₀ - 1).Coprime (primorial Y))
    (L : (PinnedShiftIndex h ⊕ PinnedShiftIndex h) → ℝ) :
    doubledFourierNormalization w (roughPinnedFourierEdges h w m p₀ Y)
        (truncatedPinnedFourierCompanion m Y) L * genericPinnedFourierSingularTail h Y =
      pinnedFiniteFourierNormalization h w m p₀ Y L := by
  have hsplit := pinnedSingularProduct_eq_finite_mul_genericTail h hm hp₀ hw hwY hYp₀ hcop
  rw [pinnedSingularSeries_preSieveCutoff_eq_inverse h hm hp₀ hwY hYp₀ hcop] at hsplit
  have hT := genericPinnedFourierSingularTail_ne_zero (Y := Y) h
    ((pinnedFourier_cutoff_large h hw).trans (by exact_mod_cast hwY))
  unfold doubledFourierNormalization pinnedFiniteFourierNormalization
  calc
    _ = ((∏ i, (L i : ℂ)) /
        ((smallDoubledFourierReferenceProduct (ι := PinnedShiftIndex h) w (fun _ _ ↦ 0))⁻¹ *
          ∏' p : Nat.Primes, roughDoubledFourierSingularFactor w
            (roughPinnedFourierEdges h w m p₀ Y) (truncatedPinnedFourierCompanion m Y) p)) *
          genericPinnedFourierSingularTail h Y := by
      simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
      ring
    _ = ((∏ i, (L i : ℂ)) /
        ((pinnedSingularSeries h w m p₀ Y : ℂ) * genericPinnedFourierSingularTail h Y)) *
          genericPinnedFourierSingularTail h Y := by rw [hsplit]
    _ = _ := by rw [div_mul_eq_div_div, div_mul_cancel₀ _ hT]

end

end Erdos4b
