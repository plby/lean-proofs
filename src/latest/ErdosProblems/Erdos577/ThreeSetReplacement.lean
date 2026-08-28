import ErdosProblems.Erdos577.ThreeContactScore
import ErdosProblems.Erdos577.LocalPathPartition

/-! A row with at least three contacts permits a replacement in any three block vertices. -/

namespace Erdos577

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma QuadOn.replace_in_three_set {a : Finset V} (ha : QuadOn G a)
    (z : V) (hz : z ∉ a) (hrow : 3 ≤ degreeIn G z a)
    (s : Finset V) (hs : s ⊆ a) (hthree : 3 ≤ s.card) :
    ∃ u ∈ s, QuadOn G (insert z (a.erase u)) := by
  by_cases hfour : degreeIn G z a = 4
  · obtain ⟨u, hu⟩ := card_pos.mp (show 0 < s.card by omega)
    exact ⟨u, hu, ha.replace_of_degree_four hz hfour (hs hu)⟩
  have hbound := degreeIn_le_card G z a
  rw [ha.card] at hbound
  have h3 : degreeIn G z a = 3 := by omega
  obtain ⟨q, rfl⟩ := ha
  obtain ⟨v, hv, hlabels⟩ := q.exists_three_contact_labels z h3
  have hout : z ∉ v.support := by rw [hv]; exact hz
  have hrep (i : Fin 4) (hi : i = 1 ∨ i = 3) :
      QuadOn G (insert z (q.support.erase (v i))) := by
    rw [← hv]
    exact v.three_contact_replace z hout hlabels i hi
  by_contra! hnone
  have hn1 : v 1 ∉ s := fun hh ↦ hnone (v 1) hh (hrep 1 (Or.inl rfl))
  have hn3 : v 3 ∉ s := fun hh ↦ hnone (v 3) hh (hrep 3 (Or.inr rfl))
  have hsub : s ⊆ {v 0, v 2} := by
    intro u hu
    obtain ⟨i, rfl⟩ := (v.mem_support u).mp (hv.symm ▸ hs hu)
    fin_cases i
    · exact mem_insert_self _ _
    · exact False.elim (hn1 hu)
    · exact mem_insert_of_mem (mem_singleton_self _)
    · exact False.elim (hn3 hu)
  have hc := card_le_card hsub
  have h02 : v 0 ≠ v 2 := v.injective.ne (by decide)
  rw [card_pair h02] at hc
  omega

lemma QuadOn.common_replacement_of_common_three {a : Finset V} (ha : QuadOn G a)
    (x y z : V) (hz : z ∉ a) (hrow : 3 ≤ degreeIn G z a)
    (hcommon : 3 ≤ ((a.filter (G.Adj x)) ∩ (a.filter (G.Adj y))).card) :
    CommonReplacement G x y z a := by
  obtain ⟨u, hu, hrep⟩ := ha.replace_in_three_set z hz hrow
    ((a.filter (G.Adj x)) ∩ (a.filter (G.Adj y)))
    (inter_subset_left.trans (filter_subset _ _)) hcommon
  obtain ⟨hx, hy⟩ := mem_inter.mp hu
  exact ⟨u, (mem_filter.mp hx).1, (mem_filter.mp hx).2, (mem_filter.mp hy).2, hrep⟩

end Erdos577
