import ErdosProblems.Erdos421.BoundedForest
import ErdosProblems.Erdos421.WeightedRawGaps
import ErdosProblems.Erdos421.WeightedUnions

/-! # Weighted mass of the bounded rejection forest -/

namespace Erdos421

theorem boundedChildren_reciprocal_sum_bound (i K H : ℕ) :
    (∑ k ∈ boundedChildren (2 ^ K) H i, (1 : ℝ) / gapLength k) ≤
      (K : ℝ) ^ 2 * H ^ 2 := by
  classical
  let I := boundedChildren (2 ^ K) H i
  have hmem : ∀ k : I, Rejected k ∧ ¬ Raw k ∧ prime (k + 1) ≤ 2 ^ K ∧
      gapLength k ≤ H ∧ parent k = i := fun k ↦ mem_boundedChildren.mp k.property
  let w : (k : I) → ParentData k :=
    fun k ↦ chosenParentData k ⟨(hmem k).1, (hmem k).2.1⟩
  have hparent : ∀ k : I, (w k).index = i := by
    intro k
    have h : Rejected k ∧ ¬ Raw k := ⟨(hmem k).1, (hmem k).2.1⟩
    have hp : parent k = (w k).index := by simp only [parent, dif_pos h, w]
    exact hp.symm.trans (hmem k).2.2.2.2
  have hL : ∀ k : I, (w k).witness.E.card ≤ K * H := fun k ↦
    ((w k).witness.length_le_log_mul_gap (hmem k).2.2.1).trans
      (Nat.mul_le_mul_left _ (hmem k).2.2.2.1)
  have hH : ∀ k : I, (w k).witness.n - (w k).witness.m + 1 ≤ H := fun k ↦
    (w k).witness.laterLength_le_gap.trans (hmem k).2.2.2.1
  have h := parentData_reciprocal_sum_bound I i K (K * H) H w hparent hL hH
    (fun k ↦ (w k).witness.length_le_log_mul_gap (hmem k).2.2.1)
  rw [Finset.sum_coe_sort I (fun k : ℕ ↦ (1 : ℝ) / gapLength k)] at h
  have heq : (K : ℝ) * (K * H : ℕ) * H = (K : ℝ) ^ 2 * H ^ 2 := by
    push_cast
    ring
  rwa [heq] at h

theorem boundedEqualDescendants_mass_le (i B H : ℕ) :
    (∑ k ∈ boundedEqualDescendants B H i, (gapLength k : ℝ)) ≤
      (H : ℝ) ^ 2 / gapLength i := by
  have h := equal_descendant_mass_mul_bound (boundedEqualDescendants B H i) i H
    (fun k hk ↦ (mem_boundedEqualDescendants.mp hk).2)
  have hg : (0 : ℝ) < gapLength i := by exact_mod_cast gapLength_pos i
  apply (le_div_iff₀ hg).mpr
  rw [mul_comm]
  exact_mod_cast h

theorem boundedSeeds_reciprocal_sum_bound (K H T : ℕ)
    (hT : 0 < T) (hB : 2 ^ K ≤ T ^ 3) :
    (∑ k ∈ boundedSeeds (2 ^ K) H, (1 : ℝ) / gapLength k) ≤
      (K : ℝ) ^ 2 * H * (3 * T ^ 2 + 1 + 2 * (K * H) ^ 2 : ℕ) +
      (boundedUnequalParents (2 ^ K) H).card * (K : ℝ) ^ 2 * H ^ 2 := by
  have hraw := raw_reciprocal_sum_bound (boundedRaw (2 ^ K) H) K H T
    (fun _ hk ↦ mem_boundedRaw.mp hk) hT hB
  have hcover := Finset.sum_le_sum_of_subset_of_nonneg (boundedSeeds_covered (2 ^ K) H)
    (f := fun k ↦ (1 : ℝ) / gapLength k) (fun _ _ _ ↦ by positivity)
  have hunion := sum_union_weight_le (boundedRaw (2 ^ K) H)
    ((boundedUnequalParents (2 ^ K) H).biUnion (boundedChildren (2 ^ K) H))
    (fun k ↦ (1 : ℝ) / gapLength k) (fun _ ↦ by positivity)
  have hchildren := sum_biUnion_weight_le (boundedUnequalParents (2 ^ K) H)
    (boundedChildren (2 ^ K) H) (fun k ↦ (1 : ℝ) / gapLength k) (fun _ ↦ by positivity)
  have hsum := Finset.sum_le_sum (s := boundedUnequalParents (2 ^ K) H)
    (fun i _ ↦ boundedChildren_reciprocal_sum_bound i K H)
  simp only [Finset.sum_const, nsmul_eq_mul] at hsum
  have h := hcover.trans (hunion.trans (add_le_add hraw (hchildren.trans hsum)))
  calc
    _ ≤ _ := h
    _ = _ := by push_cast; ring

/-- The total rejected-gap mass below an absolute cutoff. No theorem about
the distribution of primes is used in this finite estimate. -/
theorem boundedRejections_mass_bound (K H T : ℕ)
    (hT : 0 < T) (hB : 2 ^ K ≤ T ^ 3) :
    (∑ k ∈ boundedRejections (2 ^ K) H, (gapLength k : ℝ)) ≤
      (K : ℝ) ^ 2 * H ^ 3 * (3 * T ^ 2 + 1 + 2 * (K * H) ^ 2 : ℕ) +
      (boundedUnequalParents (2 ^ K) H).card * (K : ℝ) ^ 2 * H ^ 4 := by
  calc
    _ ≤ ∑ k ∈ (boundedSeeds (2 ^ K) H).biUnion (boundedEqualDescendants (2 ^ K) H),
        (gapLength k : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg (boundedRejections_covered (2 ^ K) H)
        (fun _ _ _ ↦ by positivity)
    _ ≤ ∑ i ∈ boundedSeeds (2 ^ K) H,
        ∑ k ∈ boundedEqualDescendants (2 ^ K) H i, (gapLength k : ℝ) :=
      sum_biUnion_weight_le _ _ _ (fun _ ↦ by positivity)
    _ ≤ ∑ i ∈ boundedSeeds (2 ^ K) H, (H : ℝ) ^ 2 / gapLength i :=
      Finset.sum_le_sum (fun i _ ↦ boundedEqualDescendants_mass_le i (2 ^ K) H)
    _ = (H : ℝ) ^ 2 * ∑ i ∈ boundedSeeds (2 ^ K) H, (1 : ℝ) / gapLength i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ (H : ℝ) ^ 2 *
        ((K : ℝ) ^ 2 * H * (3 * T ^ 2 + 1 + 2 * (K * H) ^ 2 : ℕ) +
          (boundedUnequalParents (2 ^ K) H).card * (K : ℝ) ^ 2 * H ^ 2) :=
      mul_le_mul_of_nonneg_left (boundedSeeds_reciprocal_sum_bound K H T hT hB) (by positivity)
    _ = _ := by ring

theorem boundedRejections_mass_bound_nat (K H T : ℕ)
    (hT : 0 < T) (hB : 2 ^ K ≤ T ^ 3) :
    (∑ k ∈ boundedRejections (2 ^ K) H, gapLength k) ≤
      K ^ 2 * H ^ 3 * (3 * T ^ 2 + 1 + 2 * (K * H) ^ 2) +
      (boundedUnequalParents (2 ^ K) H).card * K ^ 2 * H ^ 4 := by
  exact_mod_cast boundedRejections_mass_bound K H T hT hB

end Erdos421
