/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierPinnedWeightedPrimeCount
import ErdosProblems.Erdos4b.GeneralFourierPinnedCoefficientExtension
import ErdosProblems.Erdos4b.GeneralFourierPinnedSourceAsymptotic

/-!
# Source coefficients in the exact pinned prime-count estimate

The support hypotheses of the arithmetic estimate follow from the
literal source profiles. The remaining error is displayed explicitly,
before any application of a prime-distribution estimate.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

def pinnedSourceFlatCoefficient {K : ℕ} {J : Type*}
    (S : Finset J) (F : J → Fin K → ℝ → ℝ) (G : ℝ → ℝ) (h : Fin K) (LD LE : ℝ)
    (v : (PinnedShiftIndex h ⊕ PinnedShiftIndex h) → ℕ) : ℂ :=
  pinnedSourceSelbergCoefficient S F G h LD LE (fun i ↦ v (.inl i)) (fun i ↦ v (.inr i))

theorem pinnedSourceFlatCoefficient_pair_support
    {K : ℕ} {J : Type*} (S : Finset J) (F : J → Fin K → ℝ → ℝ) (G : ℝ → ℝ)
    (h : Fin K) {LD : ℝ} (hLD : 0 < LD) {Y p₀ : ℕ} (hY : 1 < Y) (hp₀ : 0 < p₀)
    (hFsupport : ∀ j ∈ S, ∀ i t, 0 ≤ t → F j i t ≠ 0 → t ≤ (1 : ℝ) / 10)
    (hGsupport : ∀ t, 0 ≤ t → G t ≠ 0 → t ≤ 1) (hD : LD / 10 < Real.log p₀)
    (d : (PinnedShiftIndex h ⊕ PinnedShiftIndex h) → Bool → ℕ)
    (hne : pinnedSourceFlatCoefficient S F G h LD (Real.log Y) (fun i ↦ d i false) *
      pinnedSourceFlatCoefficient S F G h LD (Real.log Y) (fun i ↦ d i true) ≠ 0) :
    (∀ i c, d (.inl i) c < p₀) ∧ (∀ i c, d (.inr i) c ≤ Y) := by
  have hn (c : Bool) :
      pinnedSourceFlatCoefficient S F G h LD (Real.log Y) (fun i ↦ d i c) ≠ 0 := by
    cases c
    · exact (mul_ne_zero_iff.mp hne).1
    · exact (mul_ne_zero_iff.mp hne).2
  have hs (c : Bool) := pinnedSourceSelbergCoefficient_nonzero_support S F G h hLD hY hp₀
    hFsupport hGsupport hD (fun i ↦ d (.inl i) c) (fun i ↦ d (.inr i) c) (hn c)
  exact ⟨fun i c ↦ (hs c i).2.2.1, fun i c ↦ (hs c i).2.2.2⟩

def pinnedSourcePrimeDivisorSum {K : ℕ} {J : Type*}
    (S : Finset J) (F : J → Fin K → ℝ → ℝ) (G : ℝ → ℝ) (h : Fin K)
    (P : Finset ℕ) (w m p₀ A B : ℕ) (LD LE : ℝ) : ℂ :=
  ∑ d ∈ rawDoubledCutoffDivisorTuples (PinnedShiftIndex h) P,
    (pinnedSourceFlatCoefficient S F G h LD LE (fun i ↦ d i false) *
      pinnedSourceFlatCoefficient S F G h LD LE (fun i ↦ d i true)) *
        (pinnedIntegerDivisorPrimeCount h w m p₀ A B d : ℂ)

def pinnedSourceProgressionErrorBound {K : ℕ} {J : Type*}
    (S : Finset J) (F : J → Fin K → ℝ → ℝ) (G : ℝ → ℝ) (h : Fin K)
    (P : Finset ℕ) (A B : ℕ) (LD LE : ℝ) : ℝ :=
  ∑ d ∈ rawDoubledCutoffDivisorTuples (PinnedShiftIndex h) P,
    ‖pinnedSourceFlatCoefficient S F G h LD LE (fun i ↦ d i false) *
      pinnedSourceFlatCoefficient S F G h LD LE (fun i ↦ d i true)‖ *
      (BoundedGaps.Maynard.maxProgressionDiscrepancy (B - 1) (pinnedFlatDivisorModulus h d) +
        BoundedGaps.Maynard.maxProgressionDiscrepancy (A - 1) (pinnedFlatDivisorModulus h d))

theorem norm_pinnedSourcePrimeDivisorSum_sub_graphKernel_le
    {K w m p₀ Y A B N : ℕ} {J : Type*}
    (S : Finset J) (F : J → Fin K → ℝ → ℝ) (G : ℝ → ℝ) (h : Fin K)
    {LD : ℝ} (hLD : 0 < LD) (hY : 1 < Y) (hKw : K ≤ w) (hm : 0 < m) (hp₀ : p₀.Prime)
    (hcop : (m * p₀ - 1).Coprime (primorial Y)) (hA : 0 < A) (hAB : A ≤ B)
    (hFsupport : ∀ j ∈ S, ∀ i t, 0 ≤ t → F j i t ≠ 0 → t ≤ (1 : ℝ) / 10)
    (hGsupport : ∀ t, 0 ≤ t → G t ≠ 0 → t ≤ 1) (hD : LD / 10 < Real.log p₀) :
    let P := selectedFourierPrimeCutoff (fun p ↦ decide (w < p)) (boundedFourierPrimes N)
    ‖pinnedSourcePrimeDivisorSum S F G h P w m p₀ A B LD (Real.log Y) -
      ((auxiliaryPrimeInterval A B).card : ℂ) *
        pinnedSourceTotientGraphKernel S F G h w m p₀ Y N LD (Real.log Y)‖ ≤
      pinnedSourceProgressionErrorBound S F G h P A B LD (Real.log Y) := by
  dsimp only
  apply norm_pinnedWeightedPrimeCount_sub_totientKernel_le h _
    (selectedFourierPrimeCutoff_prime _ _)
    (fun p hp ↦ rough_of_mem_selectedFourierPrimeCutoff w _ hp)
    hKw hm hp₀ hcop hA hAB
  intro d hd hne
  exact pinnedSourceFlatCoefficient_pair_support S F G h hLD hY hp₀.pos
    hFsupport hGsupport hD d hne

end

end Erdos4b
