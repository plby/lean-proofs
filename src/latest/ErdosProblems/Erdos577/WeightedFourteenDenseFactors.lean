import ErdosProblems.Erdos577.WeightedFourteenDenseTable

/-! Nine contacts force an explicit four-cycle factor once a heavy terminal is exposed. -/

namespace Erdos577.WeightedFourteen.Dense.Model.FinalTable

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

lemma common_factor (special : Fin 3) (f : (graph special).Copy G) (tag : Fin 12) (a : Finset V)
    (hd : Disjoint (univ.image f) a)
    (h : CommonReplacement G (f (triple tag 0)) (f (triple tag 2))
      (f (inserted tag)) a) : Nonempty (BlockPartition G (univ.image f ∪ a)) := by
  have hinj : Function.Injective (f : Fin 12 → V) := f.injective
  have hs : (univ \ secondBlock special tag).image f ⊆ univ.image f :=
    image_subset_image sdiff_subset
  obtain ⟨part⟩ := ((partition special tag).image f).common_partition a (hd.mono_left hs) h
  have hdis : Disjoint ((secondBlock special tag).image f)
      ((univ \ secondBlock special tag).image f ∪ a) := by
    rw [disjoint_union_right]
    refine ⟨?_, hd.mono_left (image_subset_image (subset_univ _))⟩
    rw [disjoint_image hinj]
    exact disjoint_sdiff_self_right
  have he : (secondBlock special tag).image f ∪
      ((univ \ secondBlock special tag).image f ∪ a) = univ.image f ∪ a := by
    rw [← union_assoc, ← image_union, union_sdiff_of_subset (subset_univ _)]
  exact ⟨he ▸ (BlockPartition.single ((second_quad special tag).image f)).union part hdis⟩

variable [DecidableRel G.Adj]

lemma factor_with_terminal (special : Fin 3) (f : (graph special).Copy G) (a : Finset V)
    (hd : Disjoint (univ.image f) a) (ha4 : a.card = 4)
    (h9 : 9 ≤ contacts G (terminalSet.image f) a) (x : Fin 12) (hx : x ∈ terminalSet)
    (hrep : ∀ u ∈ a, QuadOn G (insert (f x) (a.erase u))) :
    Nonempty (BlockPartition G (univ.image f ∪ a)) := by
  have hinj : Function.Injective (f : Fin 12 → V) := f.injective
  have hsum := sum_erase_add terminalSet (fun i ↦ degreeIn G (f i) a) hx
  have hdx := degreeIn_le_card G (f x) a
  rw [ha4] at hdx
  rw [contacts_image_left G terminalSet f hinj] at h9
  have h5 : 5 ≤ contacts G ((terminalSet.erase x).image f) a := by
    rw [contacts_image_left G _ f hinj]
    omega
  have hex : ∃ u ∈ a, 2 ≤ degreeIn G u ((terminalSet.erase x).image f) := by
    by_contra! hn
    have hb : (∑ u ∈ a, degreeIn G u ((terminalSet.erase x).image f)) ≤ 4 := by
      calc
        _ ≤ ∑ _ ∈ a, 1 := sum_le_sum fun u hu ↦ by have h := hn u hu; omega
        _ = 4 := by simp [ha4]
    rw [contacts_comm] at h5
    change 5 ≤ ∑ u ∈ a, degreeIn G u ((terminalSet.erase x).image f) at h5
    omega
  obtain ⟨u, hu, h2⟩ := hex
  rw [degreeIn, filter_image, card_image_of_injective _ hinj] at h2
  obtain ⟨y, hy, z, hz, hyz⟩ := one_lt_card.mp (by omega :
    1 < ((terminalSet.erase x).filter fun i ↦ G.Adj u (f i)).card)
  have hys := mem_erase.mp (mem_filter.mp hy).1
  have hzs := mem_erase.mp (mem_filter.mp hz).1
  obtain ⟨tag, htx, hend⟩ := endpoint_coverage x y z hx hys.2 hzs.2
    hys.1.symm hzs.1.symm hyz
  apply common_factor special f tag a hd
  refine ⟨u, hu, ?_, ?_, ?_⟩
  · rcases hend with ⟨hy', _⟩ | ⟨hz', _⟩
    · rw [hy']; exact (mem_filter.mp hy).2.symm
    · rw [hz']; exact (mem_filter.mp hz).2.symm
  · rcases hend with ⟨_, hz'⟩ | ⟨_, hy'⟩
    · rw [hz']; exact (mem_filter.mp hz).2.symm
    · rw [hy']; exact (mem_filter.mp hy).2.symm
  · rw [htx]
    exact hrep u hu

lemma factor_of_nine (special : Fin 3) (f : (graph special).Copy G) (a : Finset V)
    (hd : Disjoint (univ.image f) a) (ha4 : a.card = 4)
    (h9 : 9 ≤ contacts G (terminalSet.image f) a)
    (hrep : ∀ tag : Fin 4, 3 ≤ degreeIn G (f (terminalIndex tag)) a →
      ∀ u ∈ a, QuadOn G (insert (f (terminalIndex tag)) (a.erase u))) :
    Nonempty (BlockPartition G (univ.image f ∪ a)) := by
  have hinj : Function.Injective (f : Fin 12 → V) := f.injective
  have hex : ∃ x ∈ terminalSet, 3 ≤ degreeIn G (f x) a := by
    by_contra! hn
    have hb : (∑ x ∈ terminalSet, degreeIn G (f x) a) ≤ 8 := by
      calc
        _ ≤ ∑ _ ∈ terminalSet, 2 := sum_le_sum fun x hx ↦ by have h := hn x hx; omega
        _ = 8 := by simp [terminalSet_card]
    rw [contacts_image_left G terminalSet f hinj] at h9
    omega
  obtain ⟨x, hx, h3⟩ := hex
  have hxi := hx
  rw [terminalSet_eq] at hxi
  obtain ⟨tag, _, rfl⟩ := mem_image.mp hxi
  exact factor_with_terminal special f a hd ha4 h9 _ hx (hrep tag h3)

end Erdos577.WeightedFourteen.Dense.Model.FinalTable
