import ErdosProblems.Erdos587.TranslationGrowth

/-! The finite greedy subset-sum process used in CFP's homogeneous structure theorem. -/

open scoped BigOperators Pointwise

namespace Erdos587.CFP

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem subsetSum_card_add_boundary_le {B : Finset G} {a : G} (ha : a ∉ B) :
    B.subsetSum.card + translationBoundary B.subsetSum a ≤ (insert a B).subsetSum.card := by
  have hshift : translate B.subsetSum a ⊆ (insert a B).subsetSum := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨D, hDB, rfl⟩ := Finset.mem_subsetSum_iff.mp hy
    apply Finset.mem_subsetSum_iff.mpr
    refine ⟨insert a D, Finset.insert_subset_insert a hDB, ?_⟩
    rw [Finset.sum_insert (fun h => ha (hDB h))]
    exact add_comm _ _
  calc
    B.subsetSum.card + translationBoundary B.subsetSum a =
        (translate B.subsetSum a ∪ B.subsetSum).card := by
      rw [← Finset.card_sdiff_add_card]
      exact Nat.add_comm _ _
    _ ≤ (insert a B).subsetSum.card := Finset.card_le_card
      (Finset.union_subset hshift (Finset.subsetSum_mono (Finset.subset_insert a B)))

noncomputable def greedyStep (A B : Finset G) : Finset G :=
  if h : (A \ B).Nonempty then
    insert (Classical.choose ((A \ B).exists_max_image
      (translationBoundary B.subsetSum) h)) B
  else B

theorem greedyStep_spec {A B : Finset G} (h : (A \ B).Nonempty) :
    ∃ a ∈ A \ B, greedyStep A B = insert a B ∧
      ∀ x ∈ A \ B, translationBoundary B.subsetSum x ≤ translationBoundary B.subsetSum a := by
  obtain ⟨ha, hmax⟩ := Classical.choose_spec ((A \ B).exists_max_image
    (translationBoundary B.subsetSum) h)
  exact ⟨_, ha, by simp only [greedyStep, dif_pos h], hmax⟩

theorem subset_greedyStep (A B : Finset G) : B ⊆ greedyStep A B := by
  by_cases h : (A \ B).Nonempty
  · obtain ⟨a, _ha, heq, _hmax⟩ := greedyStep_spec h
    rw [heq]
    exact Finset.subset_insert a B
  · simp only [greedyStep, dif_neg h]
    exact Finset.Subset.refl _

theorem greedyStep_subset {A B : Finset G} (hBA : B ⊆ A) : greedyStep A B ⊆ A := by
  by_cases h : (A \ B).Nonempty
  · obtain ⟨a, ha, heq, _hmax⟩ := greedyStep_spec h
    rw [heq]
    exact Finset.insert_subset (Finset.mem_sdiff.mp ha).1 hBA
  · simpa only [greedyStep, dif_neg h] using hBA

theorem card_greedyStep {A B : Finset G} (h : (A \ B).Nonempty) :
    (greedyStep A B).card = B.card + 1 := by
  obtain ⟨a, ha, heq, _hmax⟩ := greedyStep_spec h
  rw [heq, Finset.card_insert_of_notMem (Finset.mem_sdiff.mp ha).2]

theorem greedyStep_growth {A B : Finset G} {k : ℕ}
    (hlarge : 2 * B.subsetSum.card ≤ (k • insert 0 (A \ B)).card) :
    (2 * k + 1) * B.subsetSum.card ≤ 2 * k * (greedyStep A B).subsetSum.card := by
  obtain ⟨a, ha, hgrowth⟩ := exists_translation_growth_of_large_nsmul
    B.subsetSum_nonempty (Finset.insert_nonempty 0 (A \ B)) hlarge
  have hapos : a ≠ 0 := by
    intro heq
    rw [heq, translationBoundary_zero, mul_zero] at hgrowth
    exact (Nat.not_le_of_gt B.subsetSum_nonempty.card_pos) hgrowth
  have haRem : a ∈ A \ B := (Finset.mem_insert.mp ha).resolve_left hapos
  obtain ⟨b, hb, hstep, hmax⟩ := greedyStep_spec (show (A \ B).Nonempty from ⟨a, haRem⟩)
  have hbound := hgrowth.trans (Nat.mul_le_mul_left (2 * k) (hmax a haRem))
  have hcard := subsetSum_card_add_boundary_le (Finset.mem_sdiff.mp hb).2
  rw [hstep]
  have hscaled := Nat.mul_le_mul_left (2 * k) hcard
  nlinarith

noncomputable def greedySubset (A : Finset G) : ℕ → Finset G
  | 0 => ∅
  | n + 1 => greedyStep A (greedySubset A n)

@[simp] theorem greedySubset_zero (A : Finset G) : greedySubset A 0 = ∅ := rfl

theorem greedySubset_succ (A : Finset G) (n : ℕ) :
    greedySubset A (n + 1) = greedyStep A (greedySubset A n) := rfl

theorem greedySubset_subset (A : Finset G) (n : ℕ) : greedySubset A n ⊆ A := by
  induction n with
  | zero => exact Finset.empty_subset A
  | succ n ih => exact greedyStep_subset ih

theorem greedySubset_mono (A : Finset G) : Monotone (greedySubset A) := by
  apply monotone_nat_of_le_succ
  intro n
  exact subset_greedyStep A (greedySubset A n)

theorem card_greedySubset_of_le (A : Finset G) {n : ℕ} (hn : n ≤ A.card) :
    (greedySubset A n).card = n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hncard := ih (by omega)
      have hrem : (A \ greedySubset A n).Nonempty := by
        apply Finset.card_pos.mp
        rw [Finset.card_sdiff_of_subset (greedySubset_subset A n), hncard]
        omega
      rw [greedySubset_succ, card_greedyStep hrem, hncard]

theorem greedySubset_growth (A : Finset G) (n k : ℕ)
    (hlarge : 2 * (greedySubset A n).subsetSum.card ≤
      (k • insert 0 (A \ greedySubset A n)).card) :
    (2 * k + 1) * (greedySubset A n).subsetSum.card ≤
      2 * k * (greedySubset A (n + 1)).subsetSum.card :=
  greedyStep_growth hlarge

/-- A fixed repeated-sum threshold gives multiplicative growth at every step. -/
theorem greedySubset_power_growth (A : Finset G) (k n : ℕ)
    (hlarge : ∀ i < n, 2 * (greedySubset A i).subsetSum.card ≤
      (k • insert 0 (A \ greedySubset A i)).card) :
    (2 * k + 1) ^ n ≤ (2 * k) ^ n * (greedySubset A n).subsetSum.card := by
  induction n with
  | zero => simp [Finset.subsetSum]
  | succ n ih =>
      have hprev := ih (fun i hi => hlarge i (by omega))
      have hstep := greedySubset_growth A n k (hlarge n (by omega))
      calc
        (2 * k + 1) ^ (n + 1) = (2 * k + 1) * (2 * k + 1) ^ n := by
          rw [pow_succ']
        _ ≤ (2 * k + 1) * ((2 * k) ^ n * (greedySubset A n).subsetSum.card) :=
          Nat.mul_le_mul_left _ hprev
        _ = (2 * k) ^ n * ((2 * k + 1) * (greedySubset A n).subsetSum.card) := by ring
        _ ≤ (2 * k) ^ n * (2 * k * (greedySubset A (n + 1)).subsetSum.card) :=
          Nat.mul_le_mul_left _ hstep
        _ = (2 * k) ^ (n + 1) * (greedySubset A (n + 1)).subsetSum.card := by
          rw [pow_succ]
          ring

end Erdos587.CFP
