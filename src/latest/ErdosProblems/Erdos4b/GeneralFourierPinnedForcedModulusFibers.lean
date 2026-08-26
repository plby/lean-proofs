/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierPinnedModulusFibers

/-!
# Grouping one forced prime with the pinned divisor coordinates

A fiber of the enlarged lcm has at most `tau(M)^(4*(K-1)+1)`
assignments. The harmless larger exponent `4*K` reuses the proved
weighted prime-level envelope with parameter `K+1`.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators ArithmeticFunction.omega

def pinnedForcedDivisorModulus {K : ℕ} (h : Fin K)
    (x : ℕ × ((PinnedShiftIndex h ⊕ PinnedShiftIndex h) → Bool → ℕ)) : ℕ :=
  Nat.lcm (pinnedFlatDivisorModulus h x.2) x.1

theorem pinnedForcedDivisorModulus_squarefree
    {K : ℕ} (h : Fin K) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (x : ℕ × ((PinnedShiftIndex h ⊕ PinnedShiftIndex h) → Bool → ℕ))
    (hp : x.1.Prime) (hd : x.2 ∈ rawDoubledCutoffDivisorTuples (PinnedShiftIndex h) P) :
    Squarefree (pinnedForcedDivisorModulus h x) := by
  classical
  have hP' : ∀ p ∈ insert x.1 P, p.Prime := by
    intro p hp'
    rcases Finset.mem_insert.mp hp' with rfl | hp'
    · exact hp
    · exact hP p hp'
  apply (primeFinsetProduct_squarefree (insert x.1 P) hP').squarefree_of_dvd
  apply Nat.lcm_dvd
  · exact (pinnedFlatDivisorModulus_dvd_cutoff h P x.2
      ((mem_rawDoubledCutoffDivisorTuples P hP x.2).mp hd)).trans
        (Finset.prod_dvd_prod_of_subset P (insert x.1 P) id (Finset.subset_insert _ _))
  · exact Finset.dvd_prod_of_mem id (Finset.mem_insert_self _ _)

theorem pinnedForcedModulusFiber_card_le_divisors_pow
    {K : ℕ} (h : Fin K) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (S : Finset (ℕ × ((PinnedShiftIndex h ⊕ PinnedShiftIndex h) → Bool → ℕ)))
    (hS : ∀ x ∈ S, x.1.Prime ∧ x.2 ∈ rawDoubledCutoffDivisorTuples (PinnedShiftIndex h) P)
    (M : ℕ) :
    (S.filter fun x ↦ pinnedForcedDivisorModulus h x = M).card ≤
      M.divisors.card ^ (4 * (K - 1) + 1) := by
  classical
  apply (Finset.card_le_card (t := M.divisors ×ˢ pinnedFlatDivisorContainer h M) ?_).trans_eq
    (by rw [Finset.card_product, pinnedFlatDivisorContainer_card, pow_succ'])
  intro x hx
  obtain ⟨hxS, hxM⟩ := Finset.mem_filter.mp hx
  have hd := hS x hxS
  have hM : M ≠ 0 := hxM ▸ (pinnedForcedDivisorModulus_squarefree h P hP x hd.1 hd.2).ne_zero
  apply Finset.mem_product.mpr
  constructor
  · exact Nat.mem_divisors.mpr ⟨hxM ▸ Nat.dvd_lcm_right (pinnedFlatDivisorModulus h x.2) x.1, hM⟩
  · simp only [pinnedFlatDivisorContainer, Fintype.mem_piFinset]
    intro i b
    exact Nat.mem_divisors.mpr
      ⟨hxM ▸ (dvd_pinnedFlatDivisorModulus h x.2 i b).trans
        (Nat.dvd_lcm_left (pinnedFlatDivisorModulus h x.2) x.1), hM⟩

theorem pinnedForcedModulusFiber_card_le_tauPow
    {K : ℕ} (h : Fin K) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (S : Finset (ℕ × ((PinnedShiftIndex h ⊕ PinnedShiftIndex h) → Bool → ℕ)))
    (hS : ∀ x ∈ S, x.1.Prime ∧ x.2 ∈ rawDoubledCutoffDivisorTuples (PinnedShiftIndex h) P)
    {M : ℕ} (hM : Squarefree M) :
    (S.filter fun x ↦ pinnedForcedDivisorModulus h x = M).card ≤ (2 ^ (4 * K)) ^ ω M := by
  apply (pinnedForcedModulusFiber_card_le_divisors_pow h P hP S hS M).trans
  rw [BoundedGaps.Maynard.card_divisors_eq_two_pow_omega hM, ← pow_mul, Nat.mul_comm (ω M), pow_mul]
  exact Nat.pow_le_pow_left (Nat.pow_le_pow_right (by norm_num) (by have := h.pos; omega)) _

theorem pinnedForcedModulusFiber_weight_le_tauPow
    {K : ℕ} (h : Fin K) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (S : Finset (ℕ × ((PinnedShiftIndex h ⊕ PinnedShiftIndex h) → Bool → ℕ)))
    (hS : ∀ x ∈ S, x.1.Prime ∧ x.2 ∈ rawDoubledCutoffDivisorTuples (PinnedShiftIndex h) P)
    (c : (ℕ × ((PinnedShiftIndex h ⊕ PinnedShiftIndex h) → Bool → ℕ)) → ℝ)
    {C : ℝ} (hC : 0 ≤ C) (hc : ∀ x ∈ S, c x ≤ C) {M : ℕ} (hM : Squarefree M) :
    (∑ x ∈ S with pinnedForcedDivisorModulus h x = M, c x) ≤
      C * (((2 ^ (4 * K)) ^ ω M : ℕ) : ℝ) := by
  calc
    _ ≤ ∑ _x ∈ S with pinnedForcedDivisorModulus h _x = M, C :=
      Finset.sum_le_sum fun x hx ↦ hc x (Finset.mem_filter.mp hx).1
    _ = C * ((S.filter fun x ↦ pinnedForcedDivisorModulus h x = M).card : ℝ) := by
      simp only [Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (by exact_mod_cast pinnedForcedModulusFiber_card_le_tauPow h P hP S hS hM) hC

theorem sum_pinnedForcedModulus_weight_le_tauPow
    {K : ℕ} (h : Fin K) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (S : Finset (ℕ × ((PinnedShiftIndex h ⊕ PinnedShiftIndex h) → Bool → ℕ)))
    (hS : ∀ x ∈ S, x.1.Prime ∧ x.2 ∈ rawDoubledCutoffDivisorTuples (PinnedShiftIndex h) P)
    (c : (ℕ × ((PinnedShiftIndex h ⊕ PinnedShiftIndex h) → Bool → ℕ)) → ℝ)
    {C : ℝ} (hC : 0 ≤ C) (hc : ∀ x ∈ S, c x ≤ C)
    (E : ℕ → ℝ) (hE : ∀ M ∈ S.image (pinnedForcedDivisorModulus h), 0 ≤ E M) :
    (∑ x ∈ S, c x * E (pinnedForcedDivisorModulus h x)) ≤
      C * ∑ M ∈ S.image (pinnedForcedDivisorModulus h),
        (((2 ^ (4 * K)) ^ ω M : ℕ) : ℝ) * E M := by
  classical
  have hmaps : ∀ x ∈ S, pinnedForcedDivisorModulus h x ∈ S.image (pinnedForcedDivisorModulus h) :=
    fun x hx ↦ Finset.mem_image.mpr ⟨x, hx, rfl⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun x ↦ c x * E (pinnedForcedDivisorModulus h x)),
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro M hM
  have hsq : Squarefree M := by
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hM
    exact pinnedForcedDivisorModulus_squarefree h P hP x (hS x hx).1 (hS x hx).2
  calc
    _ = (∑ x ∈ S with pinnedForcedDivisorModulus h x = M, c x) * E M := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x hx
      rw [(Finset.mem_filter.mp hx).2]
    _ ≤ (C * (((2 ^ (4 * K)) ^ ω M : ℕ) : ℝ)) * E M :=
      mul_le_mul_of_nonneg_right
        (pinnedForcedModulusFiber_weight_le_tauPow h P hP S hS c hC hc hsq) (hE M hM)
    _ = _ := mul_assoc _ _ _

theorem primeLevelWitness_pinnedForcedWeightedDiscrepancy_le
    {K : ℕ} (h : Fin K) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (S : Finset (ℕ × ((PinnedShiftIndex h ⊕ PinnedShiftIndex h) → Bool → ℕ)))
    (hS : ∀ x ∈ S, x.1.Prime ∧ x.2 ∈ rawDoubledCutoffDivisorTuples (PinnedShiftIndex h) P)
    (c : (ℕ × ((PinnedShiftIndex h ⊕ PinnedShiftIndex h) → Bool → ℕ)) → ℝ)
    {C₀ θ A C : ℝ} {X₀ x Q : ℕ} (hC₀ : 0 ≤ C₀) (hc : ∀ v ∈ S, c v ≤ C₀)
    (hw : BoundedGaps.Maynard.PrimeLevelWitness θ A C X₀) (hx : X₀ ≤ x)
    (hSQ : S.image (pinnedForcedDivisorModulus h) ⊆ Finset.Icc 1 Q) (hQx : Q ≤ x + 1)
    (hcut : S.image (pinnedForcedDivisorModulus h) ⊆
      Finset.Icc 1 (BoundedGaps.Maynard.modulusCutoff θ x)) :
    (∑ v ∈ S, c v * BoundedGaps.Maynard.maxProgressionDiscrepancy x
      (pinnedForcedDivisorModulus h v)) ≤ C₀ * pinnedFlatTauDiscrepancyBound (K + 1) C A x Q := by
  have hsq : ∀ M ∈ S.image (pinnedForcedDivisorModulus h), Squarefree M := by
    intro M hM
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hM
    exact pinnedForcedDivisorModulus_squarefree h P hP v (hS v hv).1 (hS v hv).2
  apply (sum_pinnedForcedModulus_weight_le_tauPow h P hP S hS c hC₀ hc
    (BoundedGaps.Maynard.maxProgressionDiscrepancy x)
    (fun M hM ↦ BoundedGaps.Maynard.maxProgressionDiscrepancy_nonneg x M)).trans
  apply mul_le_mul_of_nonneg_left _ hC₀
  simpa only [pinnedFlatTauDiscrepancyBound, Nat.add_sub_cancel] using
    hw.sum_tauPow_mul_maxProgressionDiscrepancy_explicit (d := 2 ^ (4 * K))
      hx (S.image (pinnedForcedDivisorModulus h)) hSQ hsq hQx hcut

end

end Erdos4b
