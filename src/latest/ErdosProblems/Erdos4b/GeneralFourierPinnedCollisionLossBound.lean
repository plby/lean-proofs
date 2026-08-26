/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierPinnedForcedRealBound
import ErdosProblems.Erdos4b.GeneralFourierForcedLossSum

/-!
# The normalized literal pinned collision loss

The forced main bounds and the aggregate discrepancy bound are combined
without multiplying the error by the number of forced primes.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

theorem mem_selected_rough_primeCutoff_of_le
    {w N p : ℕ} (hp : p.Prime) (hwp : w < p) (hpN : p ≤ N) :
    p ∈ selectedFourierPrimeCutoff (fun r ↦ decide (w < r)) (boundedFourierPrimes N) := by
  apply Finset.mem_image.mpr
  refine ⟨⟨p, hp⟩, Finset.mem_filter.mpr ⟨?_, ?_⟩, rfl⟩
  · exact (mem_boundedFourierPrimes N ⟨p, hp⟩).mpr hpN
  · exact decide_eq_true hwp

theorem normalized_pinnedSourceCollisionLoss_le
    {K w m p₀ Y A B : ℕ} {J : Type*}
    (S : Finset J) (F : J → Fin K → ℝ → ℝ) (G : ℝ → ℝ) (h : Fin K)
    (P : Finset ℕ) (hP : ∀ r ∈ P, r.Prime) (hrough : ∀ r ∈ P, w < r)
    (hmem : ∀ p ∈ varyingSingularPrimeSupport w Y m, p ∈ P)
    {LD C : ℝ} (hLD : 0 < LD) (hC : 0 ≤ C) (hw : 0 < w) (hY : 1 < Y)
    (hKw : K ≤ w) (hm : 0 < m) (hp₀ : p₀.Prime)
    (hcop : (m * p₀ - 1).Coprime (primorial Y)) (hA : 0 < A) (hAB : A ≤ B)
    (hFsupport : ∀ j ∈ S, ∀ i t, 0 ≤ t → F j i t ≠ 0 → t ≤ (1 : ℝ) / 10)
    (hGsupport : ∀ t, 0 ≤ t → G t ≠ 0 → t ≤ 1) (hD : LD / 10 < Real.log p₀)
    (hSS : 0 < pinnedSingularSeries h w m p₀ Y)
    (hcount : 0 < (auxiliaryPrimeInterval A B).card)
    (hmain : ∀ p ∈ varyingSingularPrimeSupport w Y m, ∀ a : ℕ,
      ‖(((LD ^ (K - 1) * Real.log Y ^ (K - 1)) /
        pinnedSingularSeries h w m p₀ Y : ℝ) : ℂ) *
          pinnedSourceForcedGraphKernel S F G h P w m p₀ Y p a LD (Real.log Y)‖ ≤ C / p) :
    let ρ := (LD ^ (K - 1) * Real.log Y ^ (K - 1)) /
      (pinnedSingularSeries h w m p₀ Y * (auxiliaryPrimeInterval A B).card)
    ρ * weightedSingularCollisionLoss K w Y m A B
      (fun q ↦ pinnedSourceRealIntegerWeight S F G h P w m p₀ q LD (Real.log Y)) ≤
      (4 * K : ℝ) * (K : ℝ) ^ 2 *
        (2 * C / w + ρ *
          pinnedSourceForcedProgressionErrorBound S F G h P Y A B LD (Real.log Y)) := by
  classical
  dsimp only
  let ρ := (LD ^ (K - 1) * Real.log Y ^ (K - 1)) /
    (pinnedSingularSeries h w m p₀ Y * (auxiliaryPrimeInterval A B).card)
  have hρ : 0 ≤ ρ := div_nonneg
    (mul_nonneg (pow_nonneg hLD.le _) (pow_nonneg (Real.log_pos (by exact_mod_cast hY)).le _))
    (mul_nonneg hSS.le (Nat.cast_nonneg _))
  let E (p : ℕ) := ρ * pinnedSourceOneForcedProgressionErrorBound S F G h P p A B LD (Real.log Y)
  have hE (p : ℕ) : 0 ≤ E p := mul_nonneg hρ
    (pinnedSourceOneForcedProgressionErrorBound_nonneg S F G h P p A B LD (Real.log Y))
  have hloss := normalized_weightedSingularCollisionLoss_le hw
    (fun q ↦ pinnedSourceRealIntegerWeight S F G h P w m p₀ q LD (Real.log Y)) hC E
    (fun p hp ↦ hE p) (ρ := ρ) (by
      intro p hp ba hba
      have hd := mem_varyingSingularPrimeSupport.mp hp
      have hne : ba.1 ≠ ba.2 := (Finset.mem_filter.mp hba).2
      rw [weightedAffineCollisionSum_eq_forced_residue hd.2.2.1 hKw hd.1 hd.2.2.2 hne]
      exact normalized_pinnedSourceRealIntegerWeight_forced_le S F G h P hP hrough
        hLD hY hKw hm hp₀ hcop (hmem p hp) (crossAffinePrimeResidue_coprime _)
        hA hAB hFsupport hGsupport hD hSS hcount (hmain p hp _))
  apply hloss.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply add_le_add le_rfl
  calc
    _ ≤ ∑ p ∈ Nat.primesLE Y, E p := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        have hd := mem_varyingSingularPrimeSupport.mp hp
        exact Nat.mem_primesLE.mpr ⟨hd.2.1, hd.2.2.1⟩
      · intro p hp hn
        exact hE p
    _ = _ := by
      simp only [E, ← Finset.mul_sum, sum_pinnedSourceOneForcedProgressionErrorBound]
      rfl

end

end Erdos4b
