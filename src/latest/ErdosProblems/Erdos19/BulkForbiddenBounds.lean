import ErdosProblems.Erdos19.CrossBulkMatching

/-! # Sizes and incidences of the forbidden sets on the bulk -/

namespace Erdos19

attribute [local instance] Classical.propDecidable

theorem compl_subtype_preimage_ncard {V : Type*} [Fintype V] (X U : Set V) :
    (Subtype.val ⁻¹' U : Set ↥(Xᶜ)).ncard = (U \ X).ncard := by
  rw [← Set.ncard_image_of_injective _ Subtype.val_injective]
  congr 1
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨hw, w.2⟩
  · rintro ⟨hu, hx⟩
    exact ⟨⟨v, hx⟩, hu, rfl⟩

theorem bulkForbidden_ncard_le {V I : Type*} [Fintype V] [Fintype I]
    (X : Set V) (active : X → Finset I) (partner : ActiveRequest active → V)
    (C : I → Set V) (i : I) :
    (bulkForbidden X active partner C i).ncard ≤ (C i).ncard + X.ncard := by
  have hpre : bulkForbidden X active partner C i =
      Subtype.val ⁻¹' (C i ∪ partnerVertices X active partner i) := rfl
  rw [hpre, compl_subtype_preimage_ncard]
  exact (Set.ncard_le_ncard Set.sdiff_subset).trans
    ((Set.ncard_union_le _ _).trans (Nat.add_le_add_left
      (partnerVertices_ncard_le X active partner i) _))

theorem bulkForbidden_color_count_le {V I : Type*} [Fintype V] [Fintype I]
    (X : Set V) (active : X → Finset I) (partner : ActiveRequest active → V)
    (C : I → Set V) (q : ℕ)
    (hquota : ∀ v, ({e : ActiveRequest active | partner e = v} : Set (ActiveRequest active)).ncard ≤ q)
    (v : ↥(Xᶜ)) :
    (∑ i : I, if v ∈ bulkForbidden X active partner C i then 1 else 0) ≤
      (∑ i : I, if v.1 ∈ C i then 1 else 0) + q := by
  have hper (i : I) : (if v ∈ bulkForbidden X active partner C i then 1 else 0) ≤
      (if v.1 ∈ C i then 1 else 0) +
        (if v.1 ∈ partnerVertices X active partner i then 1 else 0) := by
    by_cases hc : v.1 ∈ C i <;>
      by_cases hp : v.1 ∈ partnerVertices X active partner i <;>
      simp [bulkForbidden, hc, hp]
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset I)) ↦ hper i)
  rw [Finset.sum_add_distrib] at hs
  exact hs.trans (Nat.add_le_add_left (partnerVertices_color_count_le X active partner q hquota v.1) _)

#print axioms bulkForbidden_color_count_le

end Erdos19
