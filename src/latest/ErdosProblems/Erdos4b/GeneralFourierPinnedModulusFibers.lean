/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierPinnedWeightExpansion
import BoundedGaps.Maynard.ImprovedGPY.S2TrivialDiscrepancy

/-!
# Divisor-power multiplicity for the actual flat pinned modulus

Each coordinate divides the flat lcm. A modulus fiber therefore embeds
in the finite box of its divisors, independently of the prime cutoff.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators ArithmeticFunction.omega

def pinnedFlatDivisorContainer {K : ℕ} (h : Fin K) (M : ℕ) :
    Finset ((PinnedShiftIndex h ⊕ PinnedShiftIndex h) → Bool → ℕ) := by
  classical
  exact Fintype.piFinset fun _ : PinnedShiftIndex h ⊕ PinnedShiftIndex h ↦
    Fintype.piFinset fun _ : Bool ↦ M.divisors

theorem pinnedFlatDivisorContainer_card {K : ℕ} (h : Fin K) (M : ℕ) :
    (pinnedFlatDivisorContainer h M).card = M.divisors.card ^ (4 * (K - 1)) := by
  classical
  simp only [pinnedFlatDivisorContainer, Fintype.card_piFinset, Finset.prod_const,
    Finset.card_univ, Fintype.card_bool, Fintype.card_sum, card_pinnedShiftIndex, ← pow_mul]
  congr 1
  omega

theorem pinnedFlatModulusFiber_card_le_divisors_pow
    {K : ℕ} (h : Fin K) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (S : Finset ((PinnedShiftIndex h ⊕ PinnedShiftIndex h) → Bool → ℕ))
    (hS : S ⊆ rawDoubledCutoffDivisorTuples (PinnedShiftIndex h) P) (M : ℕ) :
    (S.filter fun d ↦ pinnedFlatDivisorModulus h d = M).card ≤
      M.divisors.card ^ (4 * (K - 1)) := by
  classical
  apply (Finset.card_le_card (t := pinnedFlatDivisorContainer h M) ?_).trans_eq
    (pinnedFlatDivisorContainer_card h M)
  intro d hd
  obtain ⟨hdS, hdM⟩ := Finset.mem_filter.mp hd
  have hdiv := (mem_rawDoubledCutoffDivisorTuples P hP d).mp (hS hdS)
  have hM : M ≠ 0 := by
    rw [← hdM]
    exact (pinnedFlatDivisorModulus_squarefree h P hP d hdiv).ne_zero
  simp only [pinnedFlatDivisorContainer, Fintype.mem_piFinset]
  intro i b
  apply Nat.mem_divisors.mpr
  exact ⟨hdM ▸ dvd_pinnedFlatDivisorModulus h d i b, hM⟩

theorem pinnedFlatModulusFiber_card_le_tauPow
    {K : ℕ} (h : Fin K) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (S : Finset ((PinnedShiftIndex h ⊕ PinnedShiftIndex h) → Bool → ℕ))
    (hS : S ⊆ rawDoubledCutoffDivisorTuples (PinnedShiftIndex h) P)
    {M : ℕ} (hM : Squarefree M) :
    (S.filter fun d ↦ pinnedFlatDivisorModulus h d = M).card ≤
      (2 ^ (4 * (K - 1))) ^ ω M := by
  apply (pinnedFlatModulusFiber_card_le_divisors_pow h P hP S hS M).trans_eq
  rw [BoundedGaps.Maynard.card_divisors_eq_two_pow_omega hM,
    ← pow_mul, Nat.mul_comm (ω M), pow_mul]

theorem pinnedFlatModulusFiber_weight_le_tauPow
    {K : ℕ} (h : Fin K) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (S : Finset ((PinnedShiftIndex h ⊕ PinnedShiftIndex h) → Bool → ℕ))
    (hS : S ⊆ rawDoubledCutoffDivisorTuples (PinnedShiftIndex h) P)
    (c : ((PinnedShiftIndex h ⊕ PinnedShiftIndex h) → Bool → ℕ) → ℝ)
    {C : ℝ} (hC : 0 ≤ C) (hc : ∀ d ∈ S, c d ≤ C) {M : ℕ} (hM : Squarefree M) :
    (∑ d ∈ S with pinnedFlatDivisorModulus h d = M, c d) ≤
      C * (((2 ^ (4 * (K - 1))) ^ ω M : ℕ) : ℝ) := by
  calc
    _ ≤ ∑ d ∈ S with pinnedFlatDivisorModulus h d = M, C :=
      Finset.sum_le_sum fun d hd ↦ hc d (Finset.mem_filter.mp hd).1
    _ = C * ((S.filter fun d ↦ pinnedFlatDivisorModulus h d = M).card : ℝ) := by
      simp only [Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (by exact_mod_cast pinnedFlatModulusFiber_card_le_tauPow h P hP S hS hM) hC

theorem sum_pinnedFlatModulus_weight_le_tauPow
    {K : ℕ} (h : Fin K) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (S : Finset ((PinnedShiftIndex h ⊕ PinnedShiftIndex h) → Bool → ℕ))
    (hS : S ⊆ rawDoubledCutoffDivisorTuples (PinnedShiftIndex h) P)
    (c : ((PinnedShiftIndex h ⊕ PinnedShiftIndex h) → Bool → ℕ) → ℝ)
    {C : ℝ} (hC : 0 ≤ C) (hc : ∀ d ∈ S, c d ≤ C)
    (E : ℕ → ℝ) (hE : ∀ M ∈ S.image (pinnedFlatDivisorModulus h), 0 ≤ E M) :
    (∑ d ∈ S, c d * E (pinnedFlatDivisorModulus h d)) ≤
      C * ∑ M ∈ S.image (pinnedFlatDivisorModulus h),
        (((2 ^ (4 * (K - 1))) ^ ω M : ℕ) : ℝ) * E M := by
  classical
  have hmaps : ∀ d ∈ S, pinnedFlatDivisorModulus h d ∈ S.image (pinnedFlatDivisorModulus h) :=
    fun d hd ↦ Finset.mem_image.mpr ⟨d, hd, rfl⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun d ↦ c d * E (pinnedFlatDivisorModulus h d)),
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro M hM
  have hsq : Squarefree M := by
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hM
    exact pinnedFlatDivisorModulus_squarefree h P hP d
      ((mem_rawDoubledCutoffDivisorTuples P hP d).mp (hS hd))
  calc
    _ = (∑ d ∈ S with pinnedFlatDivisorModulus h d = M, c d) * E M := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro d hd
      rw [(Finset.mem_filter.mp hd).2]
    _ ≤ (C * (((2 ^ (4 * (K - 1))) ^ ω M : ℕ) : ℝ)) * E M :=
      mul_le_mul_of_nonneg_right (pinnedFlatModulusFiber_weight_le_tauPow h P hP S hS c hC hc hsq)
        (hE M hM)
    _ = _ := mul_assoc _ _ _

def pinnedFlatTauDiscrepancyBound (K : ℕ) (C exponent : ℝ) (x Q : ℕ) : ℝ :=
  Real.sqrt ((3 : ℝ) * ((x + 1 : ℕ) : ℝ) *
    (1 + Real.log Q) ^ (2 * (2 ^ (4 * (K - 1))) ^ 2)) *
    Real.sqrt (C * (x : ℝ) / Real.rpow (Real.log (x : ℝ)) exponent)

theorem primeLevelWitness_pinnedFlatWeightedDiscrepancy_le
    {K : ℕ} (h : Fin K) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (S : Finset ((PinnedShiftIndex h ⊕ PinnedShiftIndex h) → Bool → ℕ))
    (hS : S ⊆ rawDoubledCutoffDivisorTuples (PinnedShiftIndex h) P)
    (c : ((PinnedShiftIndex h ⊕ PinnedShiftIndex h) → Bool → ℕ) → ℝ)
    {C₀ θ A C : ℝ} {X₀ x Q : ℕ} (hC₀ : 0 ≤ C₀) (hc : ∀ d ∈ S, c d ≤ C₀)
    (hw : BoundedGaps.Maynard.PrimeLevelWitness θ A C X₀) (hx : X₀ ≤ x)
    (hSQ : S.image (pinnedFlatDivisorModulus h) ⊆ Finset.Icc 1 Q) (hQx : Q ≤ x + 1)
    (hcut : S.image (pinnedFlatDivisorModulus h) ⊆
      Finset.Icc 1 (BoundedGaps.Maynard.modulusCutoff θ x)) :
    (∑ d ∈ S, c d *
      BoundedGaps.Maynard.maxProgressionDiscrepancy x (pinnedFlatDivisorModulus h d)) ≤
      C₀ * pinnedFlatTauDiscrepancyBound K C A x Q := by
  have hsq : ∀ M ∈ S.image (pinnedFlatDivisorModulus h), Squarefree M := by
    intro M hM
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hM
    exact pinnedFlatDivisorModulus_squarefree h P hP d
      ((mem_rawDoubledCutoffDivisorTuples P hP d).mp (hS hd))
  apply (sum_pinnedFlatModulus_weight_le_tauPow h P hP S hS c hC₀ hc
    (BoundedGaps.Maynard.maxProgressionDiscrepancy x)
    (fun M hM ↦ BoundedGaps.Maynard.maxProgressionDiscrepancy_nonneg x M)).trans
  exact mul_le_mul_of_nonneg_left
    (hw.sum_tauPow_mul_maxProgressionDiscrepancy_explicit (d := 2 ^ (4 * (K - 1)))
      hx (S.image (pinnedFlatDivisorModulus h)) hSQ hsq hQx hcut) hC₀

end

end Erdos4b
