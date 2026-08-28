import ErdosProblems.Erdos577.WeightedFifteenDenseTables

/-! The fourteen positive rows give an actual four-cycle factor on the enlarged local set. -/

namespace Erdos577.WeightedFifteen.DenseModel.FinalTable

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

lemma common_factor (f : graph.Copy G) (second : Bool) (tag : Fin 7) (a : Finset V)
    (hd : Disjoint (univ.image f) a)
    (h : CommonReplacement G (f (triple second tag 0)) (f (triple second tag 2))
      (f (terminal second)) a) : Nonempty (BlockPartition G (univ.image f ∪ a)) := by
  have hinj : Function.Injective (f : Fin 12 → V) := f.injective
  have hs : (univ \ secondBlock second tag).image f ⊆ univ.image f :=
    image_subset_image sdiff_subset
  obtain ⟨part⟩ := ((partition second tag).image f).common_partition a (hd.mono_left hs) h
  have hdis : Disjoint ((secondBlock second tag).image f)
      ((univ \ secondBlock second tag).image f ∪ a) := by
    rw [disjoint_union_right]
    refine ⟨?_, hd.mono_left (image_subset_image (subset_univ _))⟩
    rw [disjoint_image hinj]
    exact disjoint_sdiff_self_right
  have he : (secondBlock second tag).image f ∪
      ((univ \ secondBlock second tag).image f ∪ a) = univ.image f ∪ a := by
    rw [← union_assoc, ← image_union, union_sdiff_of_subset (subset_univ _)]
  exact ⟨he ▸ (BlockPartition.single ((second_quad second tag).image f)).union part hdis⟩

variable [DecidableRel G.Adj]

lemma factor_of_four_contacts (f : graph.Copy G) (second : Bool) (a : Finset V)
    (hd : Disjoint (univ.image f) a) (u : V) (hu : u ∈ a)
    (h4 : 4 ≤ degreeIn G u (sixSet.image f))
    (hrep : QuadOn G (insert (f (terminal second)) (a.erase u))) :
    Nonempty (BlockPartition G (univ.image f ∪ a)) := by
  have hinj : Function.Injective (f : Fin 12 → V) := f.injective
  have hx : terminal second ∈ sixSet := by cases second <;> decide +kernel
  have he := degreeIn_erase_add G u (f (terminal second)) (mem_image.mpr ⟨_, hx, rfl⟩)
  have h3 : 3 ≤ degreeIn G u ((sixSet.erase (terminal second)).image f) := by
    rw [image_erase hinj]
    split_ifs at he <;> omega
  rw [degreeIn, filter_image, card_image_of_injective _ hinj] at h3
  obtain ⟨s, hs, hs3⟩ := exists_subset_card_eq h3
  have hsp : s ∈ (sixSet.erase (terminal second)).powersetCard 3 :=
    mem_powersetCard.mpr ⟨hs.trans (filter_subset _ _), hs3⟩
  obtain ⟨tag, h0, h2⟩ := endpoint_coverage second s hsp
  exact common_factor f second tag a hd ⟨u, hu, (mem_filter.mp (hs h0)).2.symm,
    (mem_filter.mp (hs h2)).2.symm, hrep⟩

lemma factor_of_thirteen (f : graph.Copy G) (second : Bool) (a : Finset V)
    (hd : Disjoint (univ.image f) a) (ha4 : a.card = 4)
    (h13 : 13 ≤ contacts G (sixSet.image f) a)
    (hrep : ∀ u ∈ a, QuadOn G (insert (f (terminal second)) (a.erase u))) :
    Nonempty (BlockPartition G (univ.image f ∪ a)) := by
  have hex : ∃ u ∈ a, 4 ≤ degreeIn G u (sixSet.image f) := by
    by_contra! hn
    have hb : (∑ u ∈ a, degreeIn G u (sixSet.image f)) ≤ 12 := by
      calc
        _ ≤ ∑ _ ∈ a, 3 := sum_le_sum fun u hu ↦ by have h := hn u hu; omega
        _ = 12 := by simp [ha4]
    rw [contacts_comm] at h13
    change 13 ≤ ∑ u ∈ a, degreeIn G u (sixSet.image f) at h13
    omega
  obtain ⟨u, hu, h4⟩ := hex
  exact factor_of_four_contacts f second a hd u hu h4 (hrep u hu)

end Erdos577.WeightedFifteen.DenseModel.FinalTable
