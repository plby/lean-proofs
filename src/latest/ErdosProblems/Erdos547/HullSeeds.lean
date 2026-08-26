import ErdosProblems.Erdos547.TreeHull

/-!
# Adding hull branch vertices costs at most the original cut set
-/

namespace Erdos547

open Finset SimpleGraph

variable {U : Type*} [Fintype U] (T : SimpleGraph U) [DecidableRel T.Adj]

open scoped Classical in
theorem exists_hull_seed_extension (hT : T.IsTree) (W : Finset U) (hW : W.Nonempty) :
    ∃ S H : Finset U, W ⊆ S ∧ S ⊆ H ∧ S.card ≤ 2 * W.card ∧
      (T.induce (H : Set U)).Connected ∧
      ∀ u ∈ H, u ∉ S → degreeIn T H u = 2 := by
  classical
  obtain ⟨H, hWH, hH, hmin⟩ := exists_minimal_connected_hull T hT.connected W
  rcases subsingleton_or_nontrivial ↥(H : Set U) with hsingle | hnontrivial
  · letI := hsingle
    have hHcard : H.card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro u hu v hv
      exact congrArg Subtype.val (Subsingleton.elim
        (⟨u, hu⟩ : (H : Set U)) (⟨v, hv⟩ : (H : Set U)))
    have hWpos := Finset.card_pos.mpr hW
    exact ⟨H, H, hWH, Finset.Subset.refl _, by omega, hH,
      fun u hu hn ↦ (hn hu).elim⟩
  · letI := hnontrivial
    let J := T.induce (H : Set U)
    let W' : Finset ↥(H : Set U) := W.subtype (fun v ↦ v ∈ H)
    have hW'card : W'.card = W.card := by
      simp only [W', Finset.card_subtype, Finset.filter_eq_self.mpr hWH]
    have hW'deg : ∀ v : (H : Set U), v ∉ W' → 2 ≤ J.degree v := by
      intro v hv
      have hvW : v.val ∉ W := fun hh ↦ hv (Finset.mem_subtype.mpr hh)
      rw [← degreeIn_eq_induce_degree]
      exact minimal_connected_hull_degree T hW hWH hH hmin v.property hvW
    have hJ : J.IsTree := ⟨hH, hT.isAcyclic.induce _⟩
    let K' := (Finset.univ : Finset ↥(H : Set U)).filter (fun v ↦ 3 ≤ J.degree v)
    let K : Finset U := K'.image Subtype.val
    have hKcard : K.card ≤ W.card := by
      have hh := tree_branch_count J hJ W' hW'deg
      have he : K.card = K'.card := Finset.card_image_of_injective _ Subtype.val_injective
      change K'.card + 2 ≤ W'.card at hh
      omega
    let S := W ∪ K
    have hWS : W ⊆ S := Finset.subset_union_left
    have hSH : S ⊆ H := by
      intro u hu
      rcases Finset.mem_union.mp hu with huW | huK
      · exact hWH huW
      · obtain ⟨v, _, hvu⟩ := Finset.mem_image.mp huK
        exact hvu ▸ v.property
    refine ⟨S, H, hWS, hSH, ?_, hH, ?_⟩
    · have hh := Finset.card_union_le W K
      change S.card ≤ W.card + K.card at hh
      omega
    · intro u hu huS
      have huW : u ∉ W := fun hh ↦ huS (hWS hh)
      have hlo := minimal_connected_hull_degree T hW hWH hH hmin hu huW
      have hhi : ¬ 3 ≤ degreeIn T H u := by
        intro hh
        have hmem : (⟨u, hu⟩ : (H : Set U)) ∈ K' := by
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_univ _, ?_⟩
          rw [← degreeIn_eq_induce_degree]
          exact hh
        exact huS (Finset.mem_union.mpr (Or.inr
          (Finset.mem_image.mpr ⟨⟨u, hu⟩, hmem, rfl⟩)))
      omega

end Erdos547

#print axioms Erdos547.exists_hull_seed_extension
