import ErdosProblems.Erdos547.WeightedHall

/-!
# Disjoint private vertex sets from weighted Hall conditions
-/

namespace Erdos547

open Finset
open scoped BigOperators

variable {F V C : Type*} [Fintype F]

open scoped Classical in
theorem weighted_hall_of_two_class_bounds [DecidableEq C] (col : F → C) (w : F → ℕ)
    (candidates : F → Finset V)
    (hsingle : ∀ x, (∑ y ∈ (Finset.univ : Finset F).filter (fun y ↦ col y = col x), w y) ≤
      (candidates x).card)
    (hpair : ∀ x y, col x ≠ col y → (∑ z, w z) ≤ (candidates x ∪ candidates y).card) :
    ∀ J : Finset F, (∑ x ∈ J, w x) ≤ (J.biUnion candidates).card := by
  classical
  intro J
  by_cases hdiff : ∃ x ∈ J, ∃ y ∈ J, col x ≠ col y
  · obtain ⟨x, hx, y, hy, hxy⟩ := hdiff
    have hsub : candidates x ∪ candidates y ⊆ J.biUnion candidates := by
      intro v hv
      rcases Finset.mem_union.mp hv with hv | hv
      · exact Finset.mem_biUnion.mpr ⟨x, hx, hv⟩
      · exact Finset.mem_biUnion.mpr ⟨y, hy, hv⟩
    exact (Finset.sum_le_sum_of_subset (Finset.subset_univ J)).trans
      ((hpair x y hxy).trans (Finset.card_le_card hsub))
  · by_cases hJ : J.Nonempty
    · obtain ⟨x, hx⟩ := hJ
      have hsub : J ⊆ (Finset.univ : Finset F).filter (fun y ↦ col y = col x) := by
        intro y hy
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        by_contra hn
        exact hdiff ⟨y, hy, x, hx, hn⟩
      have hcan : candidates x ⊆ J.biUnion candidates :=
        fun v hv ↦ Finset.mem_biUnion.mpr ⟨x, hx, hv⟩
      exact (Finset.sum_le_sum_of_subset hsub).trans
        ((hsingle x).trans (Finset.card_le_card hcan))
    · simp only [Finset.not_nonempty_iff_eq_empty.mp hJ, Finset.sum_empty,
        Finset.biUnion_empty, Finset.card_empty, le_refl]

open scoped Classical in
theorem exists_disjoint_private_sets (w : F → ℕ) (candidates : F → Finset V)
    (hHall : ∀ J : Finset F, (∑ x ∈ J, w x) ≤ (J.biUnion candidates).card) :
    ∃ R : F → Finset V, (∀ x, R x ⊆ candidates x) ∧
      (∀ x, (R x).card = w x) ∧ Pairwise (fun x y ↦ Disjoint (R x) (R y)) := by
  classical
  let L := Σ x : F, Fin (w x)
  let parent : L → F := Sigma.fst
  have hweight (x : F) : parentWeight parent x = w x := by
    change (((Finset.univ : Finset (Σ y : F, Fin (w y))).filter
      (fun y ↦ y.1 = x)).card) = w x
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_sigma]
    simp [apply_ite]
  have hrequests := leaf_hall_of_parent_capacity parent candidates (by
    intro J
    simpa only [hweight] using hHall J)
  obtain ⟨g, hg, hgc⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective'
    (fun x : L ↦ candidates (parent x))).mp hrequests
  let R : F → Finset V := fun x ↦ (Finset.univ : Finset (Fin (w x))).image
    (fun j ↦ g ⟨x, j⟩)
  have hsub (x : F) : R x ⊆ candidates x := by
    intro v hv
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hv
    exact hgc ⟨x, j⟩
  have hcard (x : F) : (R x).card = w x := by
    have hinj : Function.Injective (fun j : Fin (w x) ↦ g ⟨x, j⟩) := by
      intro j k he
      have hh := hg he
      exact @sigma_mk_injective F (fun y ↦ Fin (w y)) x j k hh
    simp only [R, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  refine ⟨R, hsub, hcard, ?_⟩
  intro x y hxy
  apply Finset.disjoint_left.mpr
  intro v hvx hvy
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hvx
  obtain ⟨k, _, hk⟩ := Finset.mem_image.mp hvy
  exact hxy (congrArg Sigma.fst (hg (hj.trans hk.symm)))

end Erdos547

#print axioms Erdos547.exists_disjoint_private_sets
