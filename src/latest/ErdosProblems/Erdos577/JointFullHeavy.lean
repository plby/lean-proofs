import ErdosProblems.Erdos577.JointFullInside

/-! Six actual vertices, the inside budget forty-six, and a thirteen-contact outside block. -/

namespace Erdos577.JointFinal

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

def fullSix (p : Paw G) (q v : Quadrilateral G) : Finset V :=
  insert (q 3) (insert (v 3) p.support)

lemma fullSix_data (p : Paw G) (q v : Quadrilateral G)
    (hpq : Disjoint p.support q.support) (hpv : Disjoint p.support v.support)
    (hqv : Disjoint q.support v.support) :
    (fullSix p q v).card = 6 ∧ ∀ s : Finset V,
      contacts G (fullSix p q v) s =
        contacts G p.support s + degreeIn G (q 3) s + degreeIn G (v 3) s := by
  have hmQ : q 3 ∈ q.support := (q.mem_support _).mpr ⟨3, rfl⟩
  have hmV : v 3 ∈ v.support := (v.mem_support _).mpr ⟨3, rfl⟩
  have hv : v 3 ∉ p.support := fun hh ↦ disjoint_left.mp hpv hh hmV
  have hq : q 3 ∉ insert (v 3) p.support := by
    simp only [mem_insert, not_or]
    exact ⟨fun he ↦ disjoint_left.mp hqv hmQ (he.symm ▸ hmV),
      fun hh ↦ disjoint_left.mp hpq hh hmQ⟩
  refine ⟨?_, ?_⟩
  · rw [fullSix, card_insert_of_notMem hq, card_insert_of_notMem hv, p.card_support]
  · intro s
    rw [fullSix, contacts, sum_insert hq, sum_insert hv]
    change degreeIn G (q 3) s + (degreeIn G (v 3) s + contacts G p.support s) = _
    omega

variable [Fintype V]

theorem Core.full_six_inside {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    {p : Paw G} {q d : Quadrilateral G} {a j : Finset V} (h : Core c p q d a)
    (hloss : edgeCount G ((p.triangle ∪ a) \ {p.center, d 2, d 3}) < edgeCount G a)
    (hj : j ∈ c.blocks) (hjq : j ≠ q.support) (hja : j ≠ a)
    (v : Quadrilateral G) (hv : v.support = j) (z w : V)
    (hpair : z = d 2 ∧ w = d 3 ∨ z = d 3 ∧ w = d 2)
    (hpattern : FullPattern v p.leaf (q 3) z w) :
    (fullSix p q v).card = 6 ∧ contacts G (fullSix p q v) (p.support ∪ q.support ∪ a ∪ j) ≤ 46 := by
  have hd := fullSix_data p q v (h.paw_disjoint h.config.2.1)
    (by rw [hv]; exact h.paw_disjoint hj)
    (by rw [hv]; exact c.property.blocks_disjoint h.config.2.1 hj hjq.symm)
  have hp := h.full_paw_inside hc hcard hdeg hn hloss hj hjq hja v hv z w hpattern
  have hy := h.full_exposed_inside hc hcard hn hj hjq hja v hv z w hpattern
  have ht := h.full_last_inside hc hcard hn hj hjq hja v hv z w hpair hpattern
  refine ⟨hd.1, ?_⟩
  rw [hd.2]
  omega

theorem exists_thirteen_outside_three {c : TriangleChain G} {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u)
    (bs : Finset (Finset V)) (hbs : bs ⊆ c.blocks) (hbs3 : bs.card = 3)
    (s : Finset V) (hs : s.card = 6)
    (hinside : contacts G s (c.remainder ∪ bs.biUnion id) ≤ 46) :
    ∃ b ∈ c.blocks, b ∉ bs ∧ 13 ≤ contacts G s b := by
  have hblocks := c.card_vertices
  have hsub := card_sdiff_of_subset hbs
  have hge := card_le_card hbs
  obtain ⟨b, hb, hbn, hh⟩ := c.exists_heavy_outside_selected bs hbs s (2 * k) 12 hdeg (by
    rw [hs]
    omega)
  exact ⟨b, hb, hbn, Nat.succ_le_of_lt hh⟩

theorem Core.full_six_heavy {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    {p : Paw G} {q d : Quadrilateral G} {a j : Finset V} (h : Core c p q d a)
    (hloss : edgeCount G ((p.triangle ∪ a) \ {p.center, d 2, d 3}) < edgeCount G a)
    (hj : j ∈ c.blocks) (hjq : j ≠ q.support) (hja : j ≠ a)
    (v : Quadrilateral G) (hv : v.support = j) (z w : V)
    (hpair : z = d 2 ∧ w = d 3 ∨ z = d 3 ∧ w = d 2)
    (hpattern : FullPattern v p.leaf (q 3) z w) :
    ∃ b ∈ c.blocks, b ≠ q.support ∧ b ≠ a ∧ b ≠ j ∧
      13 ≤ contacts G (fullSix p q v) b := by
  obtain ⟨hsix, hinside⟩ :=
    h.full_six_inside hc hcard hdeg hn hloss hj hjq hja v hv z w hpair hpattern
  obtain ⟨hp, hq, ha, haq, _, _, _⟩ := h.config
  have hsel : ({q.support, a, j} : Finset (Finset V)) ⊆ c.blocks :=
    insert_subset hq (insert_subset ha (singleton_subset_iff.mpr hj))
  have hthree : ({q.support, a, j} : Finset (Finset V)).card = 3 :=
    card_triple_eq_three_iff.mpr ⟨haq.symm, hjq.symm, hja.symm⟩
  have he : c.remainder ∪ ({q.support, a, j} : Finset (Finset V)).biUnion id =
      p.support ∪ q.support ∪ a ∪ j := by
    simp only [biUnion_insert, singleton_biUnion, id_eq, ← hp, union_assoc]
  obtain ⟨b, hb, hbn, hh⟩ := exists_thirteen_outside_three hcard hdeg
    {q.support, a, j} hsel hthree (fullSix p q v) hsix (he.symm ▸ hinside)
  simp only [mem_insert, mem_singleton, not_or] at hbn
  exact ⟨b, hb, hbn.1, hbn.2.1, hbn.2.2, hh⟩

end Erdos577.JointFinal
