/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierPinnedForcedWeightedCount
import ErdosProblems.Erdos4b.GeneralFourierPinnedForcedUniformError
import ErdosProblems.Erdos4b.GeneralFourierPinnedPositiveWeight

/-!
# Literal pinned squares restricted to a forced prime residue

Finite Fubini gives the exact prime-count expansion; its main term is
the forced bilinear kernel with every source-profile cross term retained.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

def pinnedSourceForcedGraphKernel {K : ℕ} {J : Type*}
    (S : Finset J) (F : J → Fin K → ℝ → ℝ) (G : ℝ → ℝ) (h : Fin K)
    (P : Finset ℕ) (w m p₀ Y p a : ℕ) (LD LE : ℝ) : ℂ :=
  cutoffForcedSelbergBilinearSum P (roughPinnedFourierEdges h w m p₀ Y)
    (truncatedPinnedFourierCompanion m Y) p (PinnedForcedLocalEquations h w m p₀ p a)
    (pinnedSourceFlatCoefficient S F G h LD LE) (pinnedSourceFlatCoefficient S F G h LD LE)

def pinnedSourceOneForcedProgressionErrorBound {K : ℕ} {J : Type*}
    (S : Finset J) (F : J → Fin K → ℝ → ℝ) (G : ℝ → ℝ) (h : Fin K)
    (P : Finset ℕ) (p A B : ℕ) (LD LE : ℝ) : ℝ :=
  ∑ d ∈ rawDoubledCutoffDivisorTuples (PinnedShiftIndex h) P,
    ‖pinnedSourceFlatCoefficient S F G h LD LE (fun i ↦ d i false) *
      pinnedSourceFlatCoefficient S F G h LD LE (fun i ↦ d i true)‖ *
      (BoundedGaps.Maynard.maxProgressionDiscrepancy (B - 1) (pinnedForcedDivisorModulus h (p, d)) +
      BoundedGaps.Maynard.maxProgressionDiscrepancy (A - 1) (pinnedForcedDivisorModulus h (p, d)))

theorem sum_pinnedSourceOneForcedProgressionErrorBound
    {K : ℕ} {J : Type*} (S : Finset J) (F : J → Fin K → ℝ → ℝ) (G : ℝ → ℝ)
    (h : Fin K) (P : Finset ℕ) (Y A B : ℕ) (LD LE : ℝ) :
    (∑ p ∈ Nat.primesLE Y, pinnedSourceOneForcedProgressionErrorBound S F G h P p A B LD LE) =
      pinnedSourceForcedProgressionErrorBound S F G h P Y A B LD LE := by
  unfold pinnedSourceOneForcedProgressionErrorBound pinnedSourceForcedProgressionErrorBound
    pinnedSourceForcedEndpointErrorBound
  simp only [mul_add, Finset.sum_add_distrib]

theorem pinnedSourceOneForcedProgressionErrorBound_nonneg
    {K : ℕ} {J : Type*} (S : Finset J) (F : J → Fin K → ℝ → ℝ) (G : ℝ → ℝ)
    (h : Fin K) (P : Finset ℕ) (p A B : ℕ) (LD LE : ℝ) :
    0 ≤ pinnedSourceOneForcedProgressionErrorBound S F G h P p A B LD LE := by
  unfold pinnedSourceOneForcedProgressionErrorBound
  exact Finset.sum_nonneg fun d hd ↦ mul_nonneg (norm_nonneg _)
    (add_nonneg (BoundedGaps.Maynard.maxProgressionDiscrepancy_nonneg _ _)
      (BoundedGaps.Maynard.maxProgressionDiscrepancy_nonneg _ _))

theorem sum_pinnedSourceIntegerWeight_forced_eq_primeCount
    {K : ℕ} {J : Type*} (S : Finset J) (F : J → Fin K → ℝ → ℝ) (G : ℝ → ℝ)
    (h : Fin K) (P : Finset ℕ) (hP : ∀ r ∈ P, r.Prime)
    (w m p₀ p a A B : ℕ) (LD LE : ℝ) :
    (∑ q ∈ (auxiliaryPrimeInterval A B).filter (fun q ↦ q ≡ a [MOD p]),
      pinnedSourceIntegerWeight S F G h P w m p₀ q LD LE) =
      ∑ d ∈ rawDoubledCutoffDivisorTuples (PinnedShiftIndex h) P,
        (pinnedSourceFlatCoefficient S F G h LD LE (fun i ↦ d i false) *
          pinnedSourceFlatCoefficient S F G h LD LE (fun i ↦ d i true)) *
            (pinnedForcedIntegerPrimeCount h w m p₀ p a A B d : ℂ) := by
  classical
  simp_rw [pinnedSourceIntegerWeight_eq_raw_sum S F G h P hP]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  rw [← Finset.sum_filter]
  have hfilters : ((auxiliaryPrimeInterval A B).filter (fun q ↦ q ≡ a [MOD p])).filter
      (fun q ↦ PinnedIntegerDivisorCondition h w m p₀ q d) =
      (auxiliaryPrimeInterval A B).filter
        (fun q ↦ PinnedIntegerDivisorCondition h w m p₀ q d ∧ q ≡ a [MOD p]) := by
    ext q
    simp only [Finset.mem_filter]
    tauto
  rw [hfilters]
  simp only [Finset.sum_const, nsmul_eq_mul, pinnedForcedIntegerPrimeCount]
  ring

theorem norm_sum_pinnedSourceIntegerWeight_forced_sub_graphKernel_le
    {K w m p₀ Y p a A B : ℕ} {J : Type*}
    (S : Finset J) (F : J → Fin K → ℝ → ℝ) (G : ℝ → ℝ) (h : Fin K)
    (P : Finset ℕ) (hP : ∀ r ∈ P, r.Prime) (hrough : ∀ r ∈ P, w < r)
    {LD : ℝ} (hLD : 0 < LD) (hY : 1 < Y) (hKw : K ≤ w) (hm : 0 < m) (hp₀ : p₀.Prime)
    (hcop : (m * p₀ - 1).Coprime (primorial Y)) (hpP : p ∈ P) (ha : a.Coprime p)
    (hA : 0 < A) (hAB : A ≤ B)
    (hFsupport : ∀ j ∈ S, ∀ i t, 0 ≤ t → F j i t ≠ 0 → t ≤ (1 : ℝ) / 10)
    (hGsupport : ∀ t, 0 ≤ t → G t ≠ 0 → t ≤ 1) (hD : LD / 10 < Real.log p₀) :
    ‖(∑ q ∈ (auxiliaryPrimeInterval A B).filter (fun q ↦ q ≡ a [MOD p]),
      pinnedSourceIntegerWeight S F G h P w m p₀ q LD (Real.log Y)) -
      ((auxiliaryPrimeInterval A B).card : ℂ) *
        pinnedSourceForcedGraphKernel S F G h P w m p₀ Y p a LD (Real.log Y)‖ ≤
      pinnedSourceOneForcedProgressionErrorBound S F G h P p A B LD (Real.log Y) := by
  rw [sum_pinnedSourceIntegerWeight_forced_eq_primeCount S F G h P hP]
  apply norm_pinnedForcedWeightedPrimeCount_sub_graphKernel_le h P hP hrough hKw
    hm hp₀ hcop hpP ha hA hAB
  intro d hd hne
  exact pinnedSourceFlatCoefficient_pair_support S F G h hLD hY hp₀.pos
    hFsupport hGsupport hD d hne

theorem pinnedSourceForcedGraphKernel_eq_profile_pairs
    {K : ℕ} {J : Type*} (S : Finset J) (F : J → Fin K → ℝ → ℝ) (G : ℝ → ℝ)
    (h : Fin K) (P : Finset ℕ) (w m p₀ Y p a : ℕ) (LD LE : ℝ) :
    pinnedSourceForcedGraphKernel S F G h P w m p₀ Y p a LD LE =
      ∑ j ∈ S, ∑ k ∈ S,
        (pinnedSourceProfileAmplitude F G h j * pinnedSourceProfileAmplitude F G h k) *
          cutoffForcedSelbergProfileTensorSum P (roughPinnedFourierEdges h w m p₀ Y)
            (truncatedPinnedFourierCompanion m Y) p (PinnedForcedLocalEquations h w m p₀ p a)
            (pairedSelbergProfiles (pinnedSourceProfileFamily F G h j)
              (pinnedSourceProfileFamily F G h k)) (fun i _ ↦ twoFamilySelbergScales LD LE i) := by
  unfold pinnedSourceForcedGraphKernel pinnedSourceFlatCoefficient
  simp_rw [pinnedSourceSelbergCoefficient_eq_weighted_tensors_of_flat]
  exact cutoffForcedSelbergBilinearSum_weighted_tensors _ _ _ _ _ _ _ _ _

end

end Erdos4b
