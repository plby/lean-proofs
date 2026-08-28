import ErdosProblems.Erdos577.JointFullPartialFactors

/-! The final two five-cycle constructions exclude every full distinguished row in the loss case. -/

namespace Erdos577.JointFinal

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem Core.full_pattern_false {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    {p : Paw G} {q d : Quadrilateral G} {a j : Finset V} (h : Core c p q d a)
    (hloss : edgeCount G ((p.triangle ∪ a) \ {p.center, d 2, d 3}) < edgeCount G a)
    (hj : j ∈ c.blocks) (hjq : j ≠ q.support) (hja : j ≠ a)
    (v : Quadrilateral G) (hv : v.support = j) (z w : V)
    (hpair : z = d 2 ∧ w = d 3 ∨ z = d 3 ∧ w = d 2)
    (hpattern : FullPattern v p.leaf (q 3) z w) : False := by
  obtain ⟨b, hb, hbq, hba, hbj, hheavy⟩ :=
    h.full_six_heavy hc hcard hdeg hn hloss hj hjq hja v hv z w hpair hpattern
  have hFsmall := h.full_heavy_paw_le_eight hc hcard hdeg hn hloss hj hjq
    v hv z w hpattern hb hbq hbj hheavy
  have hy := h.full_terminal_properties hc hcard hn hj hjq v hv z w hpattern
    hb hbq hbj (q 3) (Or.inl rfl)
  have ht := h.full_terminal_properties hc hcard hn hj hjq v hv z w hpattern
    hb hbq hbj (v 3) (Or.inr rfl)
  have hsix := (fullSix_data p q v (h.paw_disjoint h.config.2.1)
    (by rw [hv]; exact h.paw_disjoint hj)
    (by rw [hv]; exact c.property.blocks_disjoint h.config.2.1 hj hjq.symm)).2 b
  rw [hsix] at hheavy
  have hyt : 5 ≤ degreeIn G (q 3) b + degreeIn G (v 3) b := by omega
  have hTsmall : contacts G p.triangle b ≤ 4 := by
    by_cases hy3 : 3 ≤ degreeIn G (q 3) b
    · exact hy.2.2.2 hy3
    · exact ht.2.2.2 (by omega)
  have hFsum := p.contacts_support b
  have hthree : 9 ≤ degreeIn G p.leaf b + degreeIn G (q 3) b + degreeIn G (v 3) b := by
    omega
  have hBcard := (c.property.blocks_quad b hb).card
  have hycap := degreeIn_le_card G (q 3) b
  have htcap := degreeIn_le_card G (v 3) b
  rw [hBcard] at hycap htcap
  have hxt : 5 ≤ degreeIn G p.leaf b + degreeIn G (v 3) b := by omega
  have hlarge : 3 ≤ degreeIn G p.leaf b ∨ 3 ≤ degreeIn G (q 3) b := by omega
  have hpairSet : ({z, w} : Finset V) = {d 2, d 3} := by
    rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact pair_comm _ _
  have harm : ({p.leaf, q 3, z, w} : Finset V) = arms p q d := by
    change insert p.leaf (insert (q 3) {z, w}) = insert p.leaf (insert (q 3) {d 2, d 3})
    rw [hpairSet]
  have hfour : ({p.leaf, q 3, z, w} : Finset V).card = 4 := by rw [harm]; exact h.arms_card
  have hzw : G.Adj z w := by
    rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h.pair_edge
    · exact h.pair_edge.symm
  have hout (u : V) (hu : u ∈ ({p.leaf, q 3, z, w} : Finset V)) : u ∉ v.support := by
    rw [hv]
    exact fun hh ↦ disjoint_left.mp (h.arms_disjoint hj hjq hja) (harm ▸ hu) hh
  have hd : Disjoint (({p.leaf, q 3, z, w} : Finset V) ∪ v.support) b := by
    rw [harm, hv]
    exact disjoint_union_left.mpr ⟨h.arms_disjoint hb hbq hba,
      c.property.blocks_disjoint hj hb hbj.symm⟩
  have hno : ¬Nonempty (BlockPartition G (({p.leaf, q 3, z, w} ∪ v.support) ∪ b)) := by
    intro parts
    apply h.arms_no_partition hc hcard hn {j, b}
      (insert_subset hj (singleton_subset_iff.mpr hb))
      (by simpa only [mem_insert, mem_singleton, not_or] using And.intro hjq.symm hbq.symm)
      (by simpa only [mem_insert, mem_singleton, not_or] using And.intro hja.symm hba.symm)
    simpa only [biUnion_insert, singleton_biUnion, id_eq, harm, hv, union_assoc] using parts
  rcases hlarge with hxlarge | hylarge
  · have hrep (t : V) (htb : t ∈ b) : QuadOn G (insert p.leaf (b.erase t)) :=
      (hc.presentPaw_feasible p h.config.1).terminal_universal_replace hb hxlarge htb
    obtain ⟨t, htb, hyt, hvt, hr⟩ :=
      JointClaims.common_replacement_of_five hBcard (q 3) (v 3) p.leaf hyt hrep
    exact hno (hpattern.old_partial hfour (hout _ (by simp)) (hout _ (by simp))
      (hout _ (by simp)) (hout _ (by simp)) hzw b hd t htb hyt.symm hvt.symm hr)
  · obtain ⟨t, htb, hxt, hvt, hr⟩ :=
      JointClaims.common_replacement_of_five hBcard p.leaf (v 3) (q 3) hxt (hy.2.2.1 hylarge)
    exact hno (hpattern.exposed_partial hfour (hout _ (by simp)) (hout _ (by simp))
      (hout _ (by simp)) (hout _ (by simp)) hzw b hd t htb hxt.symm hvt.symm hr)

theorem Core.full_distinguished_false {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    {p : Paw G} {q d : Quadrilateral G} {a j : Finset V} (h : Core c p q d a)
    (hloss : edgeCount G ((p.triangle ∪ a) \ {p.center, d 2, d 3}) < edgeCount G a)
    (hj : j ∈ c.blocks) (hjq : j ≠ q.support) (hja : j ≠ a)
    (hnine : 9 ≤ contacts G (arms p q d) j) (hpos : 1 ≤ degreeIn G p.leaf j)
    (hfull : degreeIn G (d 2) j = 4 ∨ degreeIn G (d 3) j = 4) : False := by
  obtain ⟨z, w, hpair, _, v, hv, hpattern⟩ :=
    h.exists_full_distinguished_pattern hc hcard hdeg hn hloss hj hjq hja hnine hpos hfull
  exact h.full_pattern_false hc hcard hdeg hn hloss hj hjq hja v hv z w hpair hpattern

end Erdos577.JointFinal
