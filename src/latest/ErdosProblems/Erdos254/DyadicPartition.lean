/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos254.Dyadic
import ErdosProblems.Erdos254.Partition

namespace Erdos254

open Filter Set
open scoped BigOperators

lemma blockUnion_dyadic_tail (A : Set ℕ) (k₀ : ℕ) :
    blockUnion (fun k ↦ dyadicBlock A (k₀ + k)) =
      A \ (Finset.range (2 ^ k₀ + 1) : Set ℕ) := by
  ext a
  change (∃ k, a ∈ dyadicBlock A (k₀ + k)) ↔ _
  rw [mem_dyadic_tail_iff]
  simp only [Set.mem_sdiff, Finset.mem_coe, Finset.mem_range]
  constructor
  · rintro ⟨ha, h⟩
    exact ⟨ha, by omega⟩
  · rintro ⟨ha, h⟩
    exact ⟨ha, by omega⟩

private lemma dyadic_tail_disjoint (A : Set ℕ) (k₀ : ℕ) :
    Pairwise (fun i j ↦ Disjoint (dyadicBlock A (k₀ + i)) (dyadicBlock A (k₀ + j))) :=
  fun _ _ hij ↦ dyadicBlock_pairwiseDisjoint A (by omega)

lemma selected_dyadicBlock_eq {A : Set ℕ} {k₀ : ℕ} {G : ℕ → Finset ℕ}
    (hG : ∀ k, G k ⊆ dyadicBlock A (k₀ + k)) (k : ℕ) :
    dyadicBlock (blockUnion G) (k₀ + k) = G k := by
  classical
  ext a
  constructor
  · intro ha
    rcases mem_dyadicBlock.mp ha with ⟨hlo, hhi, j, hj⟩
    have hjF := hG j hj
    have hak : a ∈ dyadicBlock A (k₀ + k) :=
      mem_dyadicBlock.mpr ⟨hlo, hhi, (mem_dyadicBlock.mp hjF).2.2⟩
    by_cases heq : j = k
    · simpa only [heq] using hj
    · exact (Finset.disjoint_left.mp (dyadic_tail_disjoint A k₀ heq) hjF hak).elim
  · intro ha
    rcases mem_dyadicBlock.mp (hG k ha) with ⟨hlo, hhi, _⟩
    exact mem_dyadicBlock.mpr ⟨hlo, hhi, k, ha⟩

lemma selected_blocks_boundedDefect {A : Set ℕ} {k₀ : ℕ} {G : ℕ → Finset ℕ}
    (hG : ∀ k, G k ⊆ dyadicBlock A (k₀ + k)) (hcard : ∀ k, 2 ≤ (G k).card) :
    HasBoundedDefect (blockUnion G) := by
  apply boundedDefect_of_two_per_dyadic (k₀ := k₀)
  intro k hk
  have heq : k = k₀ + (k - k₀) := by omega
  rw [heq, selected_dyadicBlock_eq hG]
  exact hcard _

lemma selected_blocks_infinite {A : Set ℕ} {k₀ : ℕ} {G : ℕ → Finset ℕ}
    (hG : ∀ k, G k ⊆ dyadicBlock A (k₀ + k)) (hcard : ∀ k, 1 ≤ (G k).card) :
    (blockUnion G).Infinite := by
  apply infinite_of_dyadic_count (k₀ := k₀)
  intro k hk
  have heq : k = k₀ + (k - k₀) := by omega
  rw [heq, selected_dyadicBlock_eq hG]
  exact hcard _

lemma BlockPartition.remainder_union {F : ℕ → Finset ℕ} (P : BlockPartition F)
    (hF : Pairwise (fun i j ↦ Disjoint (F i) (F j))) :
    blockUnion (fun k ↦ F k \ (P.left k ∪ P.right k)) =
      blockUnion F \ (blockUnion P.left ∪ blockUnion P.right) := by
  ext a
  constructor
  · rintro ⟨k, hk⟩
    rcases Finset.mem_sdiff.mp hk with ⟨hka, hnot⟩
    refine ⟨⟨k, hka⟩, ?_⟩
    rintro (hl | hr)
    · have : a ∈ (P.left k : Set ℕ) := by
        rw [← blockUnion_inter_block hF P.left_subset k]
        exact ⟨hl, hka⟩
      exact hnot (Finset.mem_union.mpr (Or.inl this))
    · have : a ∈ (P.right k : Set ℕ) := by
        rw [← blockUnion_inter_block hF P.right_subset k]
        exact ⟨hr, hka⟩
      exact hnot (Finset.mem_union.mpr (Or.inr this))
  · rintro ⟨⟨k, hk⟩, hnot⟩
    refine ⟨k, Finset.mem_sdiff.mpr ⟨hk, ?_⟩⟩
    intro h
    rcases Finset.mem_union.mp h with hl | hr
    · exact hnot (Or.inl ⟨k, hl⟩)
    · exact hnot (Or.inr ⟨k, hr⟩)

/-- All hypotheses of Fan's three-component criterion are obtained from the
dyadic and phase hypotheses. The union here is a finite tail of `A`. -/
theorem dyadic_three_component_partition {A : Set ℕ} {k₀ : ℕ}
    (hcard : ∀ k, k₀ ≤ k → 6 ≤ (dyadicBlock A k).card) (hdiv : PhaseDivergent A) :
    ∃ B₁ B₂ C : Set ℕ,
      B₁ ∪ B₂ ∪ C = A \ (Finset.range (2 ^ k₀ + 1) : Set ℕ) ∧
      Disjoint B₁ B₂ ∧ Disjoint B₁ C ∧ Disjoint B₂ C ∧
      B₁.Infinite ∧ B₂.Infinite ∧ C.Infinite ∧
      HasBoundedDefect B₁ ∧ HasBoundedDefect B₂ ∧ HasBoundedDefect C ∧ PhaseDivergent C := by
  classical
  let F : ℕ → Finset ℕ := fun k ↦ dyadicBlock A (k₀ + k)
  have hF : Pairwise (fun i j ↦ Disjoint (F i) (F j)) := dyadic_tail_disjoint A k₀
  have hFcard : ∀ k, 6 ≤ (F k).card := fun k ↦ hcard _ (by omega)
  have hFne : ∀ k, (F k).Nonempty := fun k ↦ Finset.card_pos.mp (by have := hFcard k; omega)
  let c : ℕ → ℕ := fun k ↦ (F k).min' (hFne k)
  have hc : ∀ k, c k ∈ F k := fun k ↦ Finset.min'_mem _ _
  have hcgeom : ∀ k, 2 ^ (k₀ + k) < c k ∧ c k ≤ 2 ^ (k₀ + k + 1) :=
    fun k ↦ ⟨(mem_dyadicBlock.mp (hc k)).1, (mem_dyadicBlock.mp (hc k)).2.1⟩
  have hcu : ∀ M, ∃ k, M < c k := by
    intro M
    refine ⟨M, ?_⟩
    have hpow : 2 ^ M ≤ 2 ^ (k₀ + M) := Nat.pow_le_pow_right (by omega) (by omega)
    exact (Nat.lt_two_pow_self.le.trans hpow).trans_lt (hcgeom M).1
  have hcratio : ∀ k, (c (k + 1) : ℝ) ≤ 4 * c k := by
    intro k
    have hlo := (hcgeom k).1
    have hhi := (hcgeom (k + 1)).2
    have hp : 2 ^ (k₀ + (k + 1) + 1) = 4 * 2 ^ (k₀ + k) := by
      rw [show k₀ + (k + 1) + 1 = (k₀ + k) + 2 by omega, pow_add]
      ring
    rw [hp] at hhi
    exact_mod_cast (show c (k + 1) ≤ 4 * c k by omega)
  have hFdiv : PhaseDivergent (blockUnion F) := by
    rw [blockUnion_dyadic_tail]
    exact hdiv.sdiff_finset _
  obtain ⟨P⟩ := exists_blockPartition F hF hFcard c hc hcu (by norm_num : (1 : ℝ) < 4) hcratio hFdiv
  let R : ℕ → Finset ℕ := fun k ↦ F k \ (P.left k ∪ P.right k)
  have hRsub : ∀ k, R k ⊆ F k := fun _ ↦ Finset.sdiff_subset
  have hRcard : ∀ k, 2 ≤ (R k).card := P.remainder_card hFcard
  have hR := P.remainder_union hF
  refine ⟨blockUnion P.left, blockUnion P.right, blockUnion R, ?_,
    disjoint_blockUnion hF P.left_subset P.right_subset P.disjoint, ?_, ?_,
    selected_blocks_infinite P.left_subset (fun k ↦ by rw [P.left_card]; omega),
    selected_blocks_infinite P.right_subset (fun k ↦ by rw [P.right_card]; omega),
    selected_blocks_infinite hRsub (fun k ↦ (by omega : 1 ≤ 2).trans (hRcard k)),
    selected_blocks_boundedDefect P.left_subset (fun k ↦ (P.left_card k).ge),
    selected_blocks_boundedDefect P.right_subset (fun k ↦ (P.right_card k).ge),
    selected_blocks_boundedDefect hRsub hRcard, ?_⟩
  · change _ ∪ _ ∪ blockUnion (fun k ↦ F k \ (P.left k ∪ P.right k)) = _
    rw [hR]
    have hsub : blockUnion P.left ∪ blockUnion P.right ⊆ blockUnion F :=
      union_subset (blockUnion_mono P.left_subset) (blockUnion_mono P.right_subset)
    rw [Set.union_comm (blockUnion P.left ∪ blockUnion P.right),
      Set.sdiff_union_of_subset hsub, blockUnion_dyadic_tail]
  · rw [show blockUnion R = _ from hR]
    exact Set.disjoint_left.mpr fun _ hl hr ↦ hr.2 (Or.inl hl)
  · rw [show blockUnion R = _ from hR]
    exact Set.disjoint_left.mpr fun _ hl hr ↦ hr.2 (Or.inr hl)
  · rw [show blockUnion R = _ from hR]
    exact P.divergent

end Erdos254
