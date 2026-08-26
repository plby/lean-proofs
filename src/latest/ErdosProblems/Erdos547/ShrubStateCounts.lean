import ErdosProblems.Erdos547.ClusterImageCount

/-!
# Occupied cluster space is bounded by the two shrub class loads
-/

namespace Erdos547.ShrubState

open Finset SimpleGraph
open scoped BigOperators

variable {U V I : Type*} [Fintype U] [DecidableEq U] [DecidableEq V]
  [DecidableEq I] {T : SimpleGraph U} [DecidableRel T.Adj] {r : U} {ℓ : ℕ}
  {col : T.Coloring (Fin 2)} {P : FineTreePartition T r ℓ col}
  {G : SimpleGraph V} {C : I → Finset V} {head : ↥P.shrubs → I}
  {seed : (T.induce (P.seeds : Set U)).Copy G}
variable (E : ShrubState P G C head seed)

noncomputable def nearUsed (i : I) : ℕ :=
  ∑ S ∈ E.placed, if head S = i then (P.nearPart S).card else 0

noncomputable def farUsed (i : I) : ℕ :=
  ∑ S ∈ E.placed, if E.tail S = i then (P.farPart S).card else 0

theorem occupied_eq_union_images : E.occupied = Finset.univ.image seed ∪
    Finset.univ.biUnion (fun S : ↥E.placed ↦ E.shrubImage S.val S.property) := by
  ext v
  rw [E.mem_occupied_iff]
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and,
    Finset.mem_biUnion, Subtype.exists]
  constructor
  · rintro (h | ⟨S, hS, hv⟩)
    · exact Or.inl h
    · exact Or.inr ⟨S, hS, hv⟩
  · rintro (h | ⟨S, hS, hv⟩)
    · exact Or.inl h
    · exact Or.inr ⟨S, hS, hv⟩

theorem shrub_cluster_card_le (hC : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (S : ↥P.shrubs) (hS : S ∈ E.placed) (i : I) :
    (C i ∩ E.shrubImage S hS).card ≤
      (if head S = i then (P.nearPart S).card else 0) +
      (if E.tail S = i then (P.farPart S).card else 0) := by
  classical
  have hh := card_cluster_image_le_two_parts C hC
    (fun v : ↥S.val ↦ E.copy (E.shrubVertex S hS v))
    (fun v : ↥S.val ↦ col v.val ≠ P.shrubColour S) (head S) (E.tail S) i
    (E.near_mem S hS) (fun v hv ↦ E.far_mem S hS v (not_not.mp hv))
  have hn := card_coe_filter_univ S.val (fun v ↦ col v ≠ P.shrubColour S)
  have hf := card_coe_filter_univ S.val (fun v ↦ col v = P.shrubColour S)
  simp only [not_not] at hh
  rw [hn, hf] at hh
  exact hh

theorem occupied_cluster_card_le (hC : ∀ i j, i ≠ j → Disjoint (C i) (C j)) (i : I) :
    (C i ∩ E.occupied).card ≤ P.seeds.card + E.nearUsed i + E.farUsed i := by
  classical
  rw [E.occupied_eq_union_images]
  have hseed : (Finset.univ.image seed).card = P.seeds.card := by
    have hi : Function.Injective (fun v : ↥P.seeds ↦ seed v) := seed.injective
    rw [Finset.card_image_of_injective _ hi, Finset.card_univ, Fintype.card_coe]
  have hh := card_inter_union_family_le (C i) (Finset.univ.image seed)
    (fun S : ↥E.placed ↦ E.shrubImage S.val S.property)
  rw [hseed] at hh
  have hs : (∑ S : ↥E.placed, (C i ∩ E.shrubImage S.val S.property).card) ≤
      E.nearUsed i + E.farUsed i := by
    calc
      _ ≤ ∑ S : ↥E.placed,
          ((if head S.val = i then (P.nearPart S.val).card else 0) +
          (if E.tail S.val = i then (P.farPart S.val).card else 0)) :=
        Finset.sum_le_sum fun S _ ↦ E.shrub_cluster_card_le hC S.val S.property i
      _ = _ := by
        rw [Finset.sum_add_distrib]
        rw [Finset.sum_coe_sort E.placed (fun S ↦ if head S = i then (P.nearPart S).card else 0)]
        rw [Finset.sum_coe_sort E.placed (fun S ↦ if E.tail S = i then (P.farPart S).card else 0)]
        rfl
  omega

end Erdos547.ShrubState

#print axioms Erdos547.ShrubState.occupied_cluster_card_le
