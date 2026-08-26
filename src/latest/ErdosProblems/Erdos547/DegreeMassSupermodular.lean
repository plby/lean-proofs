import ErdosProblems.Erdos547.DegreeExtraction

/-!
# Supermodularity of induced degree mass
-/

namespace Erdos547

open Finset SimpleGraph
open scoped BigOperators

variable {U : Type*} (G : SimpleGraph U) [DecidableRel G.Adj]

def orderedInternalEdges (S : Finset U) : Finset (U × U) :=
  (S ×ˢ S).filter (fun p ↦ G.Adj p.1 p.2)

theorem card_orderedInternalEdges (S : Finset U) :
    (orderedInternalEdges G S).card = ∑ u ∈ S, degreeIn G S u := by
  classical
  calc
    _ = ∑ p ∈ S ×ˢ S, (if G.Adj p.1 p.2 then 1 else 0 : ℕ) := by
      simp [orderedInternalEdges]
    _ = _ := by
      rw [Finset.sum_product]
      apply Finset.sum_congr rfl
      intro u _
      simp [degreeIn]

theorem degreeMass_eq_card_orderedInternalEdges (S : Finset U) :
    degreeMass G S = (orderedInternalEdges G S).card := by
  rw [card_orderedInternalEdges, degreeMass, Nat.cast_sum]

theorem degreeMass_supermodular [DecidableEq U] (A B : Finset U) :
    degreeMass G A + degreeMass G B ≤ degreeMass G (A ∪ B) + degreeMass G (A ∩ B) := by
  classical
  have hi : orderedInternalEdges G A ∩ orderedInternalEdges G B =
      orderedInternalEdges G (A ∩ B) := by
    ext p
    simp only [orderedInternalEdges, Finset.mem_inter, Finset.mem_filter, Finset.mem_product]
    tauto
  have hu : orderedInternalEdges G A ∪ orderedInternalEdges G B ⊆
      orderedInternalEdges G (A ∪ B) := by
    intro p hp
    rcases Finset.mem_union.mp hp with ha | hb
    · obtain ⟨ha, hadj⟩ := Finset.mem_filter.mp ha
      obtain ⟨ha₁, ha₂⟩ := Finset.mem_product.mp ha
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨Finset.mem_union_left _ ha₁, Finset.mem_union_left _ ha₂⟩, hadj⟩
    · obtain ⟨hb, hadj⟩ := Finset.mem_filter.mp hb
      obtain ⟨hb₁, hb₂⟩ := Finset.mem_product.mp hb
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨Finset.mem_union_right _ hb₁, Finset.mem_union_right _ hb₂⟩, hadj⟩
  have hc := Finset.card_union_add_card_inter (orderedInternalEdges G A) (orderedInternalEdges G B)
  rw [hi] at hc
  have hle := Finset.card_le_card hu
  have hn : (orderedInternalEdges G A).card + (orderedInternalEdges G B).card ≤
      (orderedInternalEdges G (A ∪ B)).card + (orderedInternalEdges G (A ∩ B)).card := by omega
  simp only [degreeMass_eq_card_orderedInternalEdges]
  exact_mod_cast hn

end Erdos547

#print axioms Erdos547.degreeMass_supermodular
