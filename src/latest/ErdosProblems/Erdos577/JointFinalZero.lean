import ErdosProblems.Erdos577.JointFinalZeroCrossing

/-! The exact local conclusion when the old leaf has no contacts in the outside block. -/

namespace Erdos577.JointFinal

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

def Conclusion (p : Paw G) (q d : Quadrilateral G) (j : Finset V) : Prop :=
  contacts G (arms p q d) j = 9 ∧ ∃ v : Quadrilateral G, v.support = j ∧
    (∀ i : Fin 4, i ≠ 0 → G.Adj (d 2) (v i) ∧ G.Adj (d 3) (v i)) ∧ G.Adj (q 3) (v 2)

theorem Core.zero_leaf_conclusion {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    {p : Paw G} {q d : Quadrilateral G} {a j : Finset V} (h : Core c p q d a)
    (hj : j ∈ c.blocks) (hjq : j ≠ q.support) (hja : j ≠ a)
    (hnine : 9 ≤ contacts G (arms p q d) j) (hzero : degreeIn G p.leaf j = 0) :
    Conclusion p q d j := by
  have hy2 := h.last_degree_le_two hc hcard hn hj hjq hja hnine
  have hsum := hnine
  rw [h.arms_contacts] at hsum
  have h1bound := degreeIn_le_card G (d 2) j
  have h2bound := degreeIn_le_card G (d 3) j
  have hjcard := (c.property.blocks_quad j hj).card
  rw [hjcard] at h1bound h2bound
  obtain ⟨jq, hjq'⟩ := c.property.blocks_quad j hj
  by_cases hy1 : degreeIn G (q 3) j = 1
  · have hfull1 := (degreeIn_eq_card_iff (G := G) (d 2) j).mp (by rw [hjcard]; omega)
    have hfull2 := (degreeIn_eq_card_iff (G := G) (d 3) j).mp (by rw [hjcard]; omega)
    obtain ⟨v, hv, hrow⟩ := jq.exists_one_contact_labels (q 3) (by rwa [hjq'])
    have hvj : (v.rotate 2).support = j := (v.rotate_support 2).trans (hv.trans hjq')
    refine ⟨?_, v.rotate 2, hvj, ?_, ?_⟩
    · rw [h.arms_contacts]
      omega
    · intro i _
      have hm : v.rotate 2 i ∈ j := hvj ▸ ((v.rotate 2).mem_support _).mpr ⟨i, rfl⟩
      exact ⟨hfull1 _ hm, hfull2 _ hm⟩
    · exact (hrow 0).mpr rfl
  · have hyexact : degreeIn G (q 3) j = 2 := by omega
    have hseven : 7 ≤ degreeIn G (d 2) j + degreeIn G (d 3) j := by omega
    have hyout : q 3 ∉ jq.support := by
      rw [hjq']
      exact fun hh ↦ disjoint_left.mp (c.property.blocks_disjoint h.config.2.1 hj hjq.symm)
        ((q.mem_support _).mpr ⟨3, rfl⟩) hh
    have hno := h.no_exposed_common hc hcard hn hj hjq hja
      (u := d 2) (v := d 3) (by simp [spokes]) (by simp [spokes])
      (d.injective.ne (by decide))
    obtain ⟨v, hv, hrow⟩ := adjacent_last_pair_labels jq (q 3) (d 2) (d 3) hyout
      (by rwa [hjq']) (by rwa [hjq']) (by rwa [hjq'])
    have hvj : v.support = j := hv.trans hjq'
    have hyv2 := (hrow 2).mpr (Or.inl rfl)
    have hyv3 := (hrow 3).mpr (Or.inr rfl)
    have hfirst := h.first_pair_not_common hc hcard hn v (by rwa [hvj])
      (by rwa [hvj]) (by rwa [hvj]) hyv2 hyv3
    have present (w : Quadrilateral G) (hw : w.support = j)
        (hmiss : ¬(G.Adj (d 2) (w 0) ∧ G.Adj (d 3) (w 0))) (hyw : G.Adj (q 3) (w 2)) :
        Conclusion p q d j := by
      obtain ⟨hsevenEq, hrows⟩ := missing_first_common_three w (d 2) (d 3) (by rwa [hw]) hmiss
      rw [hw] at hsevenEq
      refine ⟨?_, w, hw, hrows, hyw⟩
      rw [h.arms_contacts]
      omega
    by_cases h0 : G.Adj (d 2) (v 0) ∧ G.Adj (d 3) (v 0)
    · have h1 : ¬(G.Adj (d 2) (v 1) ∧ G.Adj (d 3) (v 1)) := fun hh ↦ hfirst ⟨h0, hh⟩
      exact present (v.rotate 1).reverse
        ((v.rotate 1).reverse_support.trans ((v.rotate_support 1).trans hvj)) h1 hyv3
    · exact present v hvj h0 hyv2

end Erdos577.JointFinal
