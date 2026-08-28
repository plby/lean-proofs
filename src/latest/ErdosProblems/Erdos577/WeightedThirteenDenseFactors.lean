import ErdosProblems.Erdos577.WeightedThirteenDenseTables

/-! Transport the insertion factors; five contacts from four rows force the leaf insertion. -/

namespace Erdos577.WeightedThirteen.DenseModel.FinalTable

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

lemma common_factor (f : graph.Copy G) (tag : Fin 13) (a : Finset V)
    (hd : Disjoint (univ.image f) a)
    (h : CommonReplacement G (f (triple tag 0)) (f (triple tag 2))
      (f (terminal tag)) a) : Nonempty (BlockPartition G (univ.image f ∪ a)) := by
  have hinj : Function.Injective (f : Fin 12 → V) := f.injective
  have hs : (univ \ secondBlock tag).image f ⊆ univ.image f :=
    image_subset_image sdiff_subset
  obtain ⟨part⟩ := ((partition tag).image f).common_partition a (hd.mono_left hs) h
  have hdis : Disjoint ((secondBlock tag).image f)
      ((univ \ secondBlock tag).image f ∪ a) := by
    rw [disjoint_union_right]
    refine ⟨?_, hd.mono_left (image_subset_image (subset_univ _))⟩
    rw [disjoint_image hinj]
    exact disjoint_sdiff_self_right
  have he : (secondBlock tag).image f ∪
      ((univ \ secondBlock tag).image f ∪ a) = univ.image f ∪ a := by
    rw [← union_assoc, ← image_union, union_sdiff_of_subset (subset_univ _)]
  exact ⟨he ▸ (BlockPartition.single ((second_quad tag).image f)).union part hdis⟩

variable [DecidableRel G.Adj]

lemma factor_of_five (f : graph.Copy G) (a : Finset V)
    (hd : Disjoint (univ.image f) a) (ha4 : a.card = 4)
    (h5 : 5 ≤ contacts G (fourSet.image f) a)
    (hrep : ∀ u ∈ a, QuadOn G (insert (f 0) (a.erase u))) :
    Nonempty (BlockPartition G (univ.image f ∪ a)) := by
  have hinj : Function.Injective (f : Fin 12 → V) := f.injective
  have hex : ∃ u ∈ a, 2 ≤ degreeIn G u (fourSet.image f) := by
    by_contra! hn
    have hb : (∑ u ∈ a, degreeIn G u (fourSet.image f)) ≤ 4 := by
      calc
        _ ≤ ∑ _ ∈ a, 1 := sum_le_sum fun u hu ↦ by have h := hn u hu; omega
        _ = 4 := by simp [ha4]
    rw [contacts_comm] at h5
    change 5 ≤ ∑ u ∈ a, degreeIn G u (fourSet.image f) at h5
    omega
  obtain ⟨u, hu, h2⟩ := hex
  rw [degreeIn, filter_image, card_image_of_injective _ hinj] at h2
  obtain ⟨y, hy, z, hz, hyz⟩ := one_lt_card.mp (by omega :
    1 < (fourSet.filter fun i ↦ G.Adj u (f i)).card)
  obtain ⟨tag, htag, hend⟩ := endpoint_coverage y z (mem_filter.mp hy).1 (mem_filter.mp hz).1 hyz
  apply common_factor f tag a hd
  refine ⟨u, hu, ?_, ?_, ?_⟩
  · rcases hend with ⟨hy', _⟩ | ⟨hz', _⟩
    · rw [hy']; exact (mem_filter.mp hy).2.symm
    · rw [hz']; exact (mem_filter.mp hz).2.symm
  · rcases hend with ⟨_, hz'⟩ | ⟨_, hy'⟩
    · rw [hz']; exact (mem_filter.mp hz).2.symm
    · rw [hy']; exact (mem_filter.mp hy).2.symm
  · rw [htag]
    exact hrep u hu

end Erdos577.WeightedThirteen.DenseModel.FinalTable
