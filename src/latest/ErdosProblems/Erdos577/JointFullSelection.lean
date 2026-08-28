import ErdosProblems.Erdos577.JointFullPattern

/-! Choose the exact full-row configuration in the original core and either distinguished order. -/

namespace Erdos577.JointFinal

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem Core.full_distinguished_pattern {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    {p : Paw G} {q d : Quadrilateral G} {a j : Finset V} (h : Core c p q d a)
    (hloss : edgeCount G ((p.triangle ∪ a) \ {p.center, d 2, d 3}) < edgeCount G a)
    (hj : j ∈ c.blocks) (hjq : j ≠ q.support) (hja : j ≠ a)
    (hnine : 9 ≤ contacts G (arms p q d) j) (hpos : 1 ≤ degreeIn G p.leaf j)
    (z w : V) (hpair : z = d 2 ∧ w = d 3 ∨ z = d 3 ∧ w = d 2)
    (hz : degreeIn G z j = 4) :
    contacts G (arms p q d) j = 9 ∧
      ∃ v : Quadrilateral G, v.support = j ∧ FullPattern v p.leaf (q 3) z w := by
  obtain ⟨v0, hv0⟩ := c.property.blocks_quad j hj
  have hcardj : j.card = 4 := hv0 ▸ v0.card_support
  have hfull := (degreeIn_eq_card_iff (G := G) z j).mp (hz.trans hcardj.symm)
  have included (v : Quadrilateral G) (hv : v.support = j) :
      ∀ i : Fin 4, i ≠ 3 → G.Adj z (v i) :=
    fun i _ ↦ hfull (v i) (hv ▸ (v.mem_support _).mpr ⟨i, rfl⟩)
  have hrows := h.final_rows hc hcard hdeg hn hloss hj hjq hja hnine hpos
    v0 hv0 z w hpair (included v0 hv0)
  have hx := hrows.full_old_degree (by rwa [hv0])
  obtain ⟨v1, hv1, hxrow⟩ := v0.exists_one_contact_labels p.leaf hx
  have hvj := hv1.trans hv0
  have hrows' := h.final_rows hc hcard hdeg hn hloss hj hjq hja hnine hpos
    v1 hvj z w hpair (included v1 hvj)
  obtain ⟨hsum, v, hv, hpattern⟩ := hrows'.full_first_pattern (by rwa [hvj]) hxrow
  rw [hvj] at hsum
  refine ⟨?_, v, hv.trans hvj, hpattern⟩
  rw [h.arms_contacts]
  rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hsum
  · omega

theorem Core.exists_full_distinguished_pattern {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    {p : Paw G} {q d : Quadrilateral G} {a j : Finset V} (h : Core c p q d a)
    (hloss : edgeCount G ((p.triangle ∪ a) \ {p.center, d 2, d 3}) < edgeCount G a)
    (hj : j ∈ c.blocks) (hjq : j ≠ q.support) (hja : j ≠ a)
    (hnine : 9 ≤ contacts G (arms p q d) j) (hpos : 1 ≤ degreeIn G p.leaf j)
    (hfull : degreeIn G (d 2) j = 4 ∨ degreeIn G (d 3) j = 4) :
    ∃ z w : V, (z = d 2 ∧ w = d 3 ∨ z = d 3 ∧ w = d 2) ∧
      contacts G (arms p q d) j = 9 ∧
      ∃ v : Quadrilateral G, v.support = j ∧ FullPattern v p.leaf (q 3) z w := by
  rcases hfull with hfirst | hsecond
  · exact ⟨d 2, d 3, Or.inl ⟨rfl, rfl⟩,
      h.full_distinguished_pattern hc hcard hdeg hn hloss hj hjq hja hnine hpos
        (d 2) (d 3) (Or.inl ⟨rfl, rfl⟩) hfirst⟩
  · exact ⟨d 3, d 2, Or.inr ⟨rfl, rfl⟩,
      h.full_distinguished_pattern hc hcard hdeg hn hloss hj hjq hja hnine hpos
        (d 3) (d 2) (Or.inr ⟨rfl, rfl⟩) hsecond⟩

end Erdos577.JointFinal
