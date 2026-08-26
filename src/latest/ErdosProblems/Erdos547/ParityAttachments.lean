import ErdosProblems.Erdos547.TreeAttachments
import ErdosProblems.Erdos547.HullSeedExpansion

/-!
# Equal colours at the attachments of a component
-/

namespace Erdos547

open Finset SimpleGraph

variable {U : Type*} (T : SimpleGraph U) [DecidableRel T.Adj]

theorem cut_attachment_colours_equal (hT : T.IsAcyclic) (col : T.Coloring (Fin 2))
    (C H Z : Finset U) (hC : (T.induce (C : Set U)).Connected)
    (hH : (T.induce (H : Set U)).Connected) (hZH : Z ⊆ H) (hCZ : Disjoint C Z)
    (hclosed : ∀ u ∈ Z, col u = 1 → ∀ v ∈ H, T.Adj u v → v ∈ Z)
    {u v : U} (huZ : u ∈ Z) (hvZ : v ∈ Z)
    (hu : 0 < degreeIn T C u) (hv : 0 < degreeIn T C v) : col u = col v := by
  classical
  by_cases huv : u = v
  · exact congrArg col huv
  obtain ⟨a, ha⟩ := Finset.card_pos.mp hu
  obtain ⟨haC, hua⟩ := Finset.mem_filter.mp ha
  obtain ⟨b, hb⟩ := Finset.card_pos.mp hv
  obtain ⟨hbC, hvb⟩ := Finset.mem_filter.mp hb
  have hmeet : ((C : Set U) ∩ (H : Set U)).Nonempty := by
    by_contra hn
    have hdis : Disjoint (C : Set U) (H : Set U) :=
      Set.disjoint_left.mpr (fun x hxC hxH ↦ hn ⟨x, hxC, hxH⟩)
    exact huv (forest_disjoint_subtree_attachment_unique T hT _ _ hC hH.preconnected
      hdis (hZH huZ) (hZH hvZ) haC hbC hua.symm hvb.symm)
  have hzero (z w : U) (hz : z ∈ Z) (hw : w ∈ C) (hzw : T.Adj z w) : col z = 0 := by
    have hzC : z ∉ C := fun hh ↦ Finset.disjoint_left.mp hCZ hh hz
    have hwH := forest_attachment_in_intersection T hT _ _ hC.preconnected hH.preconnected
      hmeet hw (hZH hz) hzC hzw.symm
    by_contra hn
    have hcol : col z = 1 := Fin.eq_one_of_ne_zero _ hn
    exact Finset.disjoint_left.mp hCZ hw (hclosed z hz hcol w hwH hzw)
  exact (hzero u a huZ haC hua).trans (hzero v b hvZ hbC hvb).symm

end Erdos547

#print axioms Erdos547.cut_attachment_colours_equal
