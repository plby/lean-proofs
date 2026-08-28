import ErdosProblems.Erdos577.CoreTransferHeavyShape
import ErdosProblems.Erdos577.CoreTransferMissingContact
import ErdosProblems.Erdos577.TriangleContactBounds

/-! Every qualifying outside block has exactly thirteen contacts and one fourth-vertex neighbor. -/

namespace Erdos577.CoreTransfer

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem heavy_exact {c : TriangleChain G} (hc : c.Strong) {q : Quadrilateral G}
    {bs : Finset (Finset V)} (r : Route c q bs) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    {b : Finset V} (hb : b ∈ c.blocks) (hnb : b ∉ bs)
    (hcore : LocalFactor G (insert (q 2) (c.triangle ∪ b)))
    {z : V} (hz : z ∈ c.triangle ∪ b) (hzl : G.Adj z (q 1))
    (hzrep : z ∈ b → ∃ x ∈ c.triangle, ∃ y ∈ c.triangle,
      x ≠ y ∧ G.Adj z x ∧ QuadOn G (insert y (b.erase z)))
    {a : Finset V} (ha : a ∈ c.blocks) (hna : a ∉ bs) (hab : a ≠ b)
    (hheavy : 13 ≤ contacts G (rows c q) a) :
    contacts G (rows c q) a = 13 ∧ degreeIn G (q 3) a = 1 := by
  have hbq : b ≠ q.support := fun he ↦ hnb (he ▸ r.contains_cycle)
  obtain ⟨hzero, _, h1, h3, _, hreplace⟩ :=
    heavy_shape hc r hcard hdeg hn hb hbq hcore ha hna hab hheavy
  have hid : contacts G (rows c q) a =
      contacts G c.triangle a + degreeIn G (q 1) a + degreeIn G (q 3) a := by
    rw [rows_contacts c q (r.blocks_subset r.contains_cycle), remainder_contacts, hzero, zero_add]
  have htcard : c.triangle.card = 3 := c.property.triangle_clique.card_eq
  have hacard : a.card = 4 := (c.property.blocks_quad a ha).card
  by_cases hz1 : degreeIn G (q 1) a = 0
  · have hupper := contacts_le_card_mul G c.triangle a
    rw [htcard, hacard] at hupper
    omega
  · have hpos : 0 < (a.filter (G.Adj (q 1))).card := by
      change 0 < degreeIn G (q 1) a
      omega
    obtain ⟨w, hw⟩ := card_pos.mp hpos
    obtain ⟨hwa, hlw⟩ := mem_filter.mp hw
    obtain ⟨x, hx, hxw⟩ :=
      r.missing_triangle_contact hcard hn hb hnb hz hzl hzrep ha hna hab hreplace hwa hlw
    have hupper := triangle_contacts_le_eleven_of_missing htcard hacard hx hwa hxw
    omega

end Erdos577.CoreTransfer
