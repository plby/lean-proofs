import ErdosProblems.Erdos587.NVDevelopment
import ErdosProblems.Erdos587.SubgroupStability

/-!
Deletion-stable generators give bounded, nonrepeating subset-sum witnesses
in finite quotients. Occurrences are lifted back to the original index set,
so equal images in the quotient never identify distinct available elements.
-/

open scoped BigOperators

namespace Erdos587.CFP

variable {α G H : Type*} [DecidableEq α] [AddCommGroup G] [DecidableEq G]

theorem listSubsetSums_growthTerms_eq (A : List G) :
    listSubsetSums (subsetSumGrowthTerms A) = listSubsetSums A := by
  induction A with
  | nil => simp [subsetSumGrowthTerms]
  | cons a A ih =>
    by_cases ha : addTranslate a (listSubsetSums A) = listSubsetSums A
    · simp [subsetSumGrowthTerms, ha, ih, listSubsetSums_cons]
    · simp [subsetSumGrowthTerms, ha, ih, listSubsetSums_cons]

theorem generatedSubgroup_comp [AddCommGroup H] (ψ : G →+ H) (φ : α → G) (A : Finset α) :
    generatedSubgroup (fun a => ψ (φ a)) A = (generatedSubgroup φ A).map ψ := by
  rw [generatedSubgroup, generatedSubgroup, ψ.map_closure, Set.image_image]

/-- Stable occurrences generate the same subgroup as all available indices,
and stabilize the final reachable set. Hence that whole subgroup is reached. -/
theorem mem_listSubsetSums_of_stable_generators [Fintype G]
    (φ : α → G) (A : Finset α) (r : ℕ) (hsize : Fintype.card G ≤ r + 1)
    (hstable : ∀ D ⊆ A, A.card ≤ D.card + r →
      generatedSubgroup φ D = generatedSubgroup φ A)
    {x : G} (hx : x ∈ generatedSubgroup φ A) :
    x ∈ listSubsetSums (A.toList.map φ) := by
  let s := A.toList.map φ
  obtain ⟨U, hUA, hUmap⟩ := List.sublist_map_iff.mp (subsetSumStableTerms_sublist s)
  have hUnodup : U.Nodup := A.nodup_toList.sublist hUA
  have hDA : U.toFinset ⊆ A := by
    intro a ha
    have hamem := hUA.subset (List.mem_toFinset.mp ha)
    simpa only [Finset.mem_toList] using hamem
  have hlength : U.length = (subsetSumStableTerms s).length := by
    simpa only [List.length_map] using (congrArg List.length hUmap).symm
  have hcost : A.card ≤ U.toFinset.card + r := by
    have hh := length_le_card_add_stable s
    rw [List.toFinset_card_of_nodup hUnodup, hlength]
    have hlen : s.length = A.card := by simp [s]
    rw [hlen] at hh
    omega
  have hgen := hstable U.toFinset hDA hcost
  have hsub : generatedSubgroup φ U.toFinset ≤ finsetAddStabilizer (listSubsetSums s) := by
    apply (AddSubgroup.closure_le (finsetAddStabilizer (listSubsetSums s))).mpr
    rintro y ⟨a, ha, rfl⟩
    have hamap : φ a ∈ U.map φ := List.mem_map.mpr ⟨a, List.mem_toFinset.mp ha, rfl⟩
    have hastable : φ a ∈ subsetSumStableTerms s := by rw [hUmap]; exact hamap
    exact mem_stable_stabilizes_listSubsetSums hastable
  have hxH : x ∈ finsetAddStabilizer (listSubsetSums s) := hsub (hgen.symm ▸ hx)
  have htranslate := mem_finsetAddStabilizer.mp hxH
  have hxmem : x + 0 ∈ addTranslate x (listSubsetSums s) :=
    Finset.mem_image.mpr ⟨0, zero_mem_listSubsetSums s, rfl⟩
  rw [htranslate] at hxmem
  simpa only [add_zero] using hxmem

/-- A reachable value in a finite group needs at most `|G|-1` distinct
original indices, even when the map from indices to group elements is not
injective. -/
theorem exists_small_subset_of_mem_listSubsetSums [Fintype G]
    (φ : α → G) (A : Finset α) {x : G}
    (hx : x ∈ listSubsetSums (A.toList.map φ)) :
    ∃ B ⊆ A, B.card + 1 ≤ Fintype.card G ∧ ∑ a ∈ B, φ a = x := by
  let s := A.toList.map φ
  have hx' : x ∈ listSubsetSums (subsetSumGrowthTerms s) := by
    rw [listSubsetSums_growthTerms_eq]
    exact hx
  obtain ⟨T, hT, hsum⟩ := mem_listSubsetSums_iff.mp hx'
  obtain ⟨U, hUA, hUmap⟩ :=
    List.sublist_map_iff.mp (hT.trans (subsetSumGrowthTerms_sublist s))
  have hUnodup : U.Nodup := A.nodup_toList.sublist hUA
  have hBA : U.toFinset ⊆ A := by
    intro a ha
    have hamem := hUA.subset (List.mem_toFinset.mp ha)
    simpa only [Finset.mem_toList] using hamem
  have hlength : U.length = T.length := by
    simpa only [List.length_map] using (congrArg List.length hUmap).symm
  have hcard : U.toFinset.card + 1 ≤ Fintype.card G := by
    rw [List.toFinset_card_of_nodup hUnodup, hlength]
    exact (Nat.add_le_add_right hT.length_le 1).trans
      ((growth_length_add_one_le_card_listSubsetSums s).trans (Finset.card_le_univ _))
  refine ⟨U.toFinset, hBA, hcard, ?_⟩
  rw [List.sum_toFinset φ hUnodup, ← hUmap]
  exact hsum

theorem exists_small_subset_sum_of_stable_generators [Fintype G]
    (φ : α → G) (A : Finset α) (r : ℕ) (hsize : Fintype.card G ≤ r + 1)
    (hstable : ∀ D ⊆ A, A.card ≤ D.card + r →
      generatedSubgroup φ D = generatedSubgroup φ A)
    {x : G} (hx : x ∈ generatedSubgroup φ A) :
    ∃ B ⊆ A, B.card + 1 ≤ Fintype.card G ∧ ∑ a ∈ B, φ a = x :=
  exists_small_subset_of_mem_listSubsetSums φ A
    (mem_listSubsetSums_of_stable_generators φ A r hsize hstable hx)

/-- Finite-index residue adjustment using actual distinct available indices. -/
theorem exists_small_subset_sum_mod_subgroup
    (φ : α → G) (A : Finset α) (Δ : AddSubgroup G) [Δ.FiniteIndex]
    (r : ℕ) (hsize : Δ.index ≤ r + 1)
    (hstable : ∀ D ⊆ A, A.card ≤ D.card + r →
      generatedSubgroup φ D = generatedSubgroup φ A)
    {x : G} (hx : x ∈ generatedSubgroup φ A) :
    ∃ B ⊆ A, B.card + 1 ≤ Δ.index ∧ (∑ a ∈ B, φ a) - x ∈ Δ := by
  classical
  let : Fintype (G ⧸ Δ) := Fintype.ofFinite _
  let ψ := QuotientAddGroup.mk' Δ
  have hcard : Fintype.card (G ⧸ Δ) = Δ.index := by
    simp only [AddSubgroup.index, Nat.card_eq_fintype_card]
  have hstable' : ∀ D ⊆ A, A.card ≤ D.card + r →
      generatedSubgroup (fun a => ψ (φ a)) D = generatedSubgroup (fun a => ψ (φ a)) A := by
    intro D hDA hcost
    rw [generatedSubgroup_comp, generatedSubgroup_comp, hstable D hDA hcost]
  have hx' : ψ x ∈ generatedSubgroup (fun a => ψ (φ a)) A := by
    rw [generatedSubgroup_comp]
    exact AddSubgroup.mem_map.mpr ⟨x, hx, rfl⟩
  obtain ⟨B, hBA, hcardB, hsum⟩ := exists_small_subset_sum_of_stable_generators
    (fun a => ψ (φ a)) A r (by simpa only [hcard] using hsize) hstable' hx'
  refine ⟨B, hBA, hcardB.trans_eq hcard, ?_⟩
  have heq : ψ (∑ a ∈ B, φ a) = ψ x := by simpa only [map_sum] using hsum
  simpa only [sub_eq_add_neg, add_comm] using QuotientAddGroup.eq.mp heq.symm

end Erdos587.CFP
