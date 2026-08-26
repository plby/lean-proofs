import ErdosProblems.Erdos547.TreeConvexity
import ErdosProblems.Erdos547.FiniteTreeBoundary

/-!
# At most two attachments after cutting all hull branch vertices
-/

namespace Erdos547

open Finset SimpleGraph

variable {U : Type*} (T : SimpleGraph U)

theorem forest_attachment_in_intersection (hT : T.IsAcyclic) (C H : Set U)
    (hC : (T.induce C).Preconnected) (hH : (T.induce H).Preconnected)
    (hmeet : (C ∩ H).Nonempty) {u v : U} (hu : u ∈ C) (hv : v ∈ H)
    (hvC : v ∉ C) (huv : T.Adj u v) : u ∈ H := by
  obtain ⟨x, hxC, hxH⟩ := hmeet
  obtain ⟨q, hq⟩ := hC.exists_isPath ⟨u, hu⟩ ⟨x, hxC⟩
  let f : (T.induce C) →g T := { toFun := Subtype.val, map_rel' := fun h ↦ h }
  let p := q.map f
  have hp : p.IsPath := hq.map Subtype.val_injective
  have hps := forest_path_subset_of_preconnected T hT C hC hu hxC p hp
  have hvp : v ∉ p.support := fun hh ↦ hvC (hps v hh)
  have hpath : (p.cons huv.symm).IsPath := hp.cons hvp
  apply forest_path_subset_of_preconnected T hT H hH hv hxH (p.cons huv.symm) hpath u
  simp only [Walk.support_cons, List.mem_cons]
  exact Or.inr p.start_mem_support

theorem forest_disjoint_subtree_attachment_unique (hT : T.IsAcyclic) (C H : Set U)
    (hC : (T.induce C).Connected) (hH : (T.induce H).Preconnected)
    (hdis : Disjoint C H) {u v a b : U} (hu : u ∈ H) (hv : v ∈ H)
    (ha : a ∈ C) (hb : b ∈ C) (hau : T.Adj a u) (hbv : T.Adj b v) : u = v := by
  by_contra hne
  have hc' := connected_induce_insert (T := T) C hC u ⟨a, ha⟩ hau.symm
  have hvC : v ∉ C := fun hh ↦ Set.disjoint_left.mp hdis hh hv
  have hv' : v ∉ insert u C := by
    intro hh
    rcases Set.mem_insert_iff.mp hh with hh | hh
    · exact hne hh.symm
    · exact hvC hh
  have hbH := forest_attachment_in_intersection T hT (insert u C) H hc'.preconnected hH
    ⟨u, Set.mem_insert _ _, hu⟩ (Set.mem_insert_of_mem _ hb) hv hv' hbv
  exact Set.disjoint_left.mp hdis hb hbH

open scoped Classical in
theorem card_cut_neighbours_le_two [DecidableRel T.Adj] (hT : T.IsAcyclic)
    (C H W : Finset U) (hC : (T.induce (C : Set U)).Connected)
    (hH : (T.induce (H : Set U)).Connected) (hWH : W ⊆ H) (hCW : Disjoint C W)
    (hdeg : ∀ u ∈ H, u ∉ W → degreeIn T H u ≤ 2) :
    (W.filter (fun v ↦ 0 < degreeIn T C v)).card ≤ 2 := by
  classical
  by_cases hmeet : ((C : Set U) ∩ (H : Set U)).Nonempty
  · let I := C ∩ H
    have hIconn : (T.induce (I : Set U)).Connected := by
      have heq : (I : Set U) = (C : Set U) ∩ (H : Set U) := by
        ext u
        exact Finset.mem_inter
      rw [heq]
      exact forest_connected_inter T hT _ _ hC.preconnected hH.preconnected hmeet
    have hItree : (T.induce (I : Set U)).IsTree := ⟨hIconn, hT.induce _⟩
    have hIH : I ⊆ H := Finset.inter_subset_right
    have hIdegrees : ∀ u ∈ I, degreeIn T H u ≤ 2 := by
      intro u hu
      have hh := Finset.mem_inter.mp hu
      exact hdeg u hh.2 (fun hw ↦ Finset.disjoint_left.mp hCW hh.1 hw)
    have hsub : W.filter (fun v ↦ 0 < degreeIn T C v) ⊆
        (H \ I).filter (fun v ↦ 0 < degreeIn T I v) := by
      intro v hv
      obtain ⟨hvW, hpos⟩ := Finset.mem_filter.mp hv
      have hvC : v ∉ C := fun hh ↦ Finset.disjoint_left.mp hCW hh hvW
      obtain ⟨u, hu⟩ := Finset.card_pos.mp hpos
      obtain ⟨hu, hvu⟩ := Finset.mem_filter.mp hu
      have huH := forest_attachment_in_intersection T hT _ _ hC.preconnected hH.preconnected
        hmeet hu (hWH hvW) hvC hvu.symm
      refine Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr
        ⟨hWH hvW, fun hh ↦ hvC (Finset.mem_inter.mp hh).1⟩, ?_⟩
      exact Finset.card_pos.mpr ⟨u, Finset.mem_filter.mpr
        ⟨Finset.mem_inter.mpr ⟨hu, huH⟩, hvu⟩⟩
    exact (Finset.card_le_card hsub).trans
      (card_boundary_le_two_of_degreeIn_le_two T hItree hIH hIdegrees)
  · have hdis : Disjoint (C : Set U) (H : Set U) := Set.disjoint_left.mpr
        (fun u huC huH ↦ hmeet ⟨u, huC, huH⟩)
    have hcard : (W.filter (fun v ↦ 0 < degreeIn T C v)).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro u hu v hv
      obtain ⟨huW, hu⟩ := Finset.mem_filter.mp hu
      obtain ⟨hvW, hv⟩ := Finset.mem_filter.mp hv
      obtain ⟨a, ha⟩ := Finset.card_pos.mp hu
      obtain ⟨ha, hua⟩ := Finset.mem_filter.mp ha
      obtain ⟨b, hb⟩ := Finset.card_pos.mp hv
      obtain ⟨hb, hvb⟩ := Finset.mem_filter.mp hb
      exact forest_disjoint_subtree_attachment_unique T hT _ _ hC hH.preconnected hdis
        (hWH huW) (hWH hvW) ha hb hua.symm hvb.symm
    omega

end Erdos547

#print axioms Erdos547.card_cut_neighbours_le_two
