import ErdosProblems.Erdos547.ShrubColours

/-!
# Summing the two colour-class sizes of the shrubs
-/

namespace Erdos547

open Finset SimpleGraph
open scoped BigOperators

theorem sum_disjoint_filtered_sizes {U : Type*} [DecidableEq U]
    (F : Finset (Finset U)) (p : U → Prop) [DecidablePred p]
    (hdis : ∀ S ∈ F, ∀ Q ∈ F, S ≠ Q → Disjoint S Q) :
    (∑ S : ↥F, (S.val.filter p).card) = ((F.biUnion id).filter p).card := by
  classical
  rw [Finset.sum_coe_sort F (fun S ↦ (S.filter p).card), Finset.filter_biUnion]
  rw [Finset.card_biUnion (show (F : Set (Finset U)).PairwiseDisjoint
    (fun S ↦ (id S).filter p) from
    fun S hS Q hQ hne ↦ (hdis S hS Q hQ hne).mono
      (Finset.filter_subset _ _) (Finset.filter_subset _ _))]
  rfl

namespace FineTreePartition

variable {U : Type*} [Fintype U] [DecidableEq U] {T : SimpleGraph U}
  [DecidableRel T.Adj] {r : U} {ℓ : ℕ} {col : T.Coloring (Fin 2)}
variable (P : FineTreePartition T r ℓ col)

open scoped Classical in
theorem sum_near_shrub_sizes (i : Fin 2) :
    (∑ S : ↥(P.shrubsOfColour i), (S.val.filter (fun v ↦ col v ≠ i)).card) =
      (P.nearVertices i).card := by
  classical
  apply sum_disjoint_filtered_sizes
  intro S hS Q hQ hne
  exact P.disjoint_shrubs S (Finset.mem_filter.mp hS).1 Q (Finset.mem_filter.mp hQ).1 hne

open scoped Classical in
theorem sum_far_shrub_sizes (i : Fin 2) :
    (∑ S : ↥(P.shrubsOfColour i), (S.val.filter (fun v ↦ col v = i)).card) =
      (P.farVertices i).card := by
  classical
  apply sum_disjoint_filtered_sizes
  intro S hS Q hQ hne
  exact P.disjoint_shrubs S (Finset.mem_filter.mp hS).1 Q (Finset.mem_filter.mp hQ).1 hne

theorem seed_colour_surjective (hne : ∀ i, (P.nearVertices i).Nonempty) :
    Function.Surjective (fun z : ↥P.seeds ↦ col z.val) := by
  classical
  intro i
  obtain ⟨v, hv⟩ := hne i
  have hvunion : v ∈ P.shrubVertices i := (Finset.mem_filter.mp hv).1
  obtain ⟨S, hS, _hvS⟩ := Finset.mem_biUnion.mp hvunion
  obtain ⟨z, hz, hdeg⟩ := P.has_attachment S (Finset.mem_filter.mp hS).1
  exact ⟨⟨z, hz⟩, (Finset.mem_filter.mp hS).2 z hz hdeg⟩

end FineTreePartition

end Erdos547

#print axioms Erdos547.FineTreePartition.sum_near_shrub_sizes
#print axioms Erdos547.FineTreePartition.seed_colour_surjective
