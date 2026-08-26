import ErdosProblems.Erdos547.AttachmentPath
import ErdosProblems.Erdos547.ShortPathClosure

/-!
# Consecutive cut vertices are separated in tree distance
-/

namespace Erdos547

open Finset SimpleGraph

theorem cut_attachment_distance_lower {U : Type*} (T : SimpleGraph U) [DecidableRel T.Adj]
    (hT : T.IsAcyclic) (C H Z : Finset U) (hC : (T.induce (C : Set U)).Preconnected)
    (hH : (T.induce (H : Set U)).Preconnected) (hZH : Z ⊆ H) (hCZ : Disjoint C Z)
    (hlong : ∀ a ∈ Z, ∀ b ∈ Z, a ≠ b → ∀ p : T.Walk a b, p.IsPath → 2 ≤ p.length →
      (∀ u ∈ p.support, u ∈ H) → (∀ u ∈ p.support, u ∈ Z → u = a ∨ u = b) → 6 ≤ p.length)
    {u v : U} (huZ : u ∈ Z) (hvZ : v ∈ Z) (huv : u ≠ v)
    (hu : 0 < degreeIn T C u) (hv : 0 < degreeIn T C v) : 6 ≤ T.dist u v := by
  classical
  obtain ⟨a, ha⟩ := Finset.card_pos.mp hu
  obtain ⟨haC, hua⟩ := Finset.mem_filter.mp ha
  obtain ⟨b, hb⟩ := Finset.card_pos.mp hv
  obtain ⟨hbC, hvb⟩ := Finset.mem_filter.mp hb
  have huC : u ∉ C := fun hh ↦ Finset.disjoint_left.mp hCZ hh huZ
  have hvC : v ∉ C := fun hh ↦ Finset.disjoint_left.mp hCZ hh hvZ
  obtain ⟨p, hp, hl, hs⟩ := exists_path_through_connected_piece T hT _ hC huC hvC huv
    haC hbC hua hvb
  have hsupport : ∀ w ∈ p.support, w ∈ H :=
    forest_path_subset_of_preconnected T hT _ hH (hZH huZ) (hZH hvZ) p hp
  have hcuts : ∀ w ∈ p.support, w ∈ Z → w = u ∨ w = v := by
    intro w hw hwZ
    rcases hs w hw with hh | hh | hh
    · exact Or.inl hh
    · exact Or.inr hh
    · exact (Finset.disjoint_left.mp hCZ hh hwZ).elim
  have hlen := hlong u huZ v hvZ huv p hp hl hsupport hcuts
  rwa [forest_path_length_eq_dist T hT p hp] at hlen

end Erdos547

#print axioms Erdos547.cut_attachment_distance_lower
