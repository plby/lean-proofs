import ErdosProblems.Erdos577.JointFullTerminals

/-! Original core maximality excludes nine paw contacts on the thirteen-contact outside block. -/

namespace Erdos577.JointFinal

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem Core.full_heavy_paw_le_eight {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    {p : Paw G} {q d : Quadrilateral G} {a j b : Finset V} (h : Core c p q d a)
    (hloss : edgeCount G ((p.triangle ∪ a) \ {p.center, d 2, d 3}) < edgeCount G a)
    (hj : j ∈ c.blocks) (hjq : j ≠ q.support)
    (v : Quadrilateral G) (hv : v.support = j) (z w : V)
    (hpattern : FullPattern v p.leaf (q 3) z w)
    (hb : b ∈ c.blocks) (hbq : b ≠ q.support) (hbj : b ≠ j)
    (hheavy : 13 ≤ contacts G (fullSix p q v) b) : contacts G p.support b ≤ 8 := by
  obtain ⟨hp, hq, _, _, hcase, _, _⟩ := h.config
  have hy := h.full_terminal_properties hc hcard hn hj hjq v hv z w hpattern
    hb hbq hbj (q 3) (Or.inl rfl)
  have ht := h.full_terminal_properties hc hcard hn hj hjq v hv z w hpattern
    hb hbq hbj (v 3) (Or.inr rfl)
  have hsix := (fullSix_data p q v (h.paw_disjoint hq)
    (by rw [hv]; exact h.paw_disjoint hj)
    (by rw [hv]; exact c.property.blocks_disjoint hq hj hjq.symm)).2 b
  rw [hsix] at hheavy
  have hqm : q 3 ∈ q.support := (q.mem_support _).mpr ⟨3, rfl⟩
  have hvm : v 3 ∈ j := hv ▸ (v.mem_support _).mpr ⟨3, rfl⟩
  have hout (u : V) (hu : u = q 3 ∨ u = v 3) : u ∉ p.support ∪ b := by
    rcases hu with hu | hu
    · subst u
      intro hh
      rcases mem_union.mp hh with hh | hh
      · exact disjoint_left.mp (h.paw_disjoint hq) hh hqm
      · exact disjoint_left.mp (c.property.blocks_disjoint hq hb hbq.symm) hqm hh
    · subst u
      intro hh
      rcases mem_union.mp hh with hh | hh
      · exact disjoint_left.mp (h.paw_disjoint hj) hh hvm
      · exact disjoint_left.mp (c.property.blocks_disjoint hj hb hbj.symm) hvm hh
  by_contra! hlarge
  have hFheavy : 9 ≤ contacts G p.support b := by omega
  have hxzero : degreeIn G p.leaf b = 0 := by
    by_contra hxne
    have hxpos : 0 < degreeIn G p.leaf b := by omega
    have heq := (JointClaims.heavy_positive_counts hc hcard hdeg hn p hp hb hFheavy hxpos).2.1
    have hchoice : 2 ≤ degreeIn G (q 3) b ∨ 2 ≤ degreeIn G (v 3) b := by omega
    rcases hchoice with hY | hV
    · exact hy.1 (JointClaims.heavy_positive_outside_factor hc hcard hdeg hn p hp hb
        hFheavy hxpos (q 3) (hout (q 3) (Or.inl rfl)) hY)
    · exact ht.1 (JointClaims.heavy_positive_outside_factor hc hcard hdeg hn p hp hb
        hFheavy hxpos (v 3) (hout (v 3) (Or.inr rfl)) hV)
  have hFsum := p.contacts_support b
  have hTdense : 9 ≤ contacts G p.triangle b := by omega
  have hyone := hy.2.1 hTdense
  have htone := ht.2.1 hTdense
  have hTeleven : 11 ≤ contacts G p.triangle b := by omega
  have hBcard := (c.property.blocks_quad b hb).card
  have hrcap := degreeIn_le_card G p.center b
  have hbcap := degreeIn_le_card G (p.vertices 2) b
  rw [hBcard] at hrcap hbcap
  have hTsum := p.contacts_triangle b
  change contacts G p.triangle b = degreeIn G p.center b +
    (degreeIn G (p.vertices 2) b + degreeIn G (p.vertices 3) b) at hTsum
  have houter : 7 ≤ degreeIn G p.center b + degreeIn G (p.vertices 3) b := by omega
  have hweight : 13 ≤ degreeIn G (p.vertices 3) b + contacts G p.triangle b := by omega
  have hcandidate : JointClaims.CaseTwoCore c p q b :=
    ⟨hp, hq, hb, hbq, hcase, houter, hweight⟩
  have hmax := h.maximal.2.1 b hcandidate
  have hTA := (h.loss_scores hloss).2.2.1
  omega

end Erdos577.JointFinal
