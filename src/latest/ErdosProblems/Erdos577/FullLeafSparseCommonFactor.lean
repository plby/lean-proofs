import ErdosProblems.Erdos577.FullLeafSparseFirstUnique

/-! Ten contacts on each complete block turn shared neighboring columns into three cycles. -/

namespace Erdos577.FullLeafSparse

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem common_column_factor_of_ten {t j l : Finset V} {v d e x : V}
    (ht : t.card = 3) (hj : G.IsNClique 4 j) (hl : G.IsNClique 4 l)
    (hd : Disjoint t (j ∪ l)) (hjl : Disjoint j l) (hv : v ∉ t ∪ (j ∪ l))
    (hdj : d ∈ j) (hel : e ∈ l) (hvd : G.Adj v d) (hve : G.Adj v e)
    (hJ : 10 ≤ contacts G t j) (hL : 10 ≤ contacts G t l)
    (hx : x ∈ t) (hxd : G.Adj x d) (hxe : G.Adj x e) :
    Nonempty (BlockPartition G (insert v (t ∪ (j ∪ l)))) := by
  have hout (w : V) (hw : w ∈ t) : w ∉ j ∧ w ∉ l :=
    ⟨fun hh ↦ disjoint_left.mp hd hw (mem_union_left _ hh),
      fun hh ↦ disjoint_left.mp hd hw (mem_union_right _ hh)⟩
  have finish (i u w : V) (henum : t = {i, u, w})
      (hiu : i ≠ u) (hiw : i ≠ w) (huw : u ≠ w)
      (hid : G.Adj i d) (hie : G.Adj i e)
      (hrepJ : QuadOn G (insert u (j.erase d)))
      (hrepL : QuadOn G (insert w (l.erase e))) :
      Nonempty (BlockPartition G (insert v (t ∪ (j ∪ l)))) := by
    have hf := common_column_partition (henum ▸ hd) hjl (henum ▸ hv)
      hiu hiw huw hdj hel hvd hid hie hve hrepJ hrepL
    simpa only [← henum] using hf
  obtain ⟨y, hy, hyx, hyRow⟩ := high_row_ne_of_ten ht hj.card_eq hJ hx
  obtain ⟨z, hz, hxz, hyz, henum⟩ := triple_third_of_two ht hx hy hyx.symm
  have hrepJ := clique_replace_of_degree_three hj (hout y hy).1 hyRow hdj
  by_cases hrepL : QuadOn G (insert z (l.erase e))
  · exact finish x y z henum hyx.symm hxz hyz hxd hxe hrepJ hrepL
  have htwoJ : 2 ≤ degreeIn G z j := by
    have hb := contacts_le_other_rows (G := G) (j := j) hz
    rw [ht, hj.card_eq] at hb
    omega
  have htwoL : 2 ≤ degreeIn G z l := by
    have hb := contacts_le_other_rows (G := G) (j := l) hz
    rw [ht, hl.card_eq] at hb
    omega
  have hrowL : degreeIn G z l = 2 := by
    by_contra hh
    exact hrepL (clique_replace_of_degree_three hl (hout z hz).2 (by omega) hel)
  have hze : G.Adj z e := by
    by_contra hnot
    have heq := degreeIn_erase_add G z e hel
    rw [hrowL, if_neg hnot, add_zero] at heq
    exact hrepL ((clique_replace_iff_two_contacts hl (hout z hz).2 hel).mpr (by omega))
  have hsum : contacts G t l = degreeIn G x l + degreeIn G y l + degreeIn G z l := by
    rw [henum, contacts]
    simp [hyx.symm, hxz, hyz, add_assoc]
  have hxbound := degreeIn_le_card G x l
  have hybound := degreeIn_le_card G y l
  rw [hl.card_eq] at hxbound hybound
  have hxFull : degreeIn G x l = 4 := by omega
  have hyFull : degreeIn G y l = 4 := by omega
  by_cases hzd : G.Adj z d
  · have hperm : t = {z, y, x} := by
      rw [henum]
      ext u
      simp only [mem_insert, mem_singleton]
      tauto
    exact finish z y x hperm hyz.symm hxz.symm hyx hzd hze hrepJ
      (clique_replace_of_degree_three hl (hout x hx).2 (by omega) hel)
  · have hrepZ : QuadOn G (insert z (j.erase d)) := by
      apply (clique_replace_iff_two_contacts hj (hout z hz).1 hdj).mpr
      have heq := degreeIn_erase_add G z d hdj
      rw [if_neg hzd, add_zero] at heq
      omega
    have hperm : t = {x, z, y} := by
      rw [henum]
      ext u
      simp only [mem_insert, mem_singleton]
      tauto
    exact finish x z y hperm hxz hyx.symm hyz.symm hxd hxe hrepZ
      (clique_replace_of_degree_three hl (hout y hy).2 (by omega) hel)

end Erdos577.FullLeafSparse
