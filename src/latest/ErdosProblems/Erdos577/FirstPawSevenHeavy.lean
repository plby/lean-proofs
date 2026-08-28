import ErdosProblems.Erdos577.FirstPawSevenUpper
import ErdosProblems.Erdos577.OutsideCoreCount
import ErdosProblems.Erdos577.PawInduced

/-! The four distinguished rows have inside sum at most13
and an outside block with nine contacts. -/

namespace Erdos577.FirstPawSeven

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

def rows (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support) : Finset V :=
  weightSet.image (PawEncoding.labeling p q hd)

omit [DecidableRel G.Adj] in
lemma rows_card (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support) :
    (rows p q hd).card = 4 := by
  rw [rows, card_image_of_injective _ (PawEncoding.labeling p q hd).injective, weightSet_card]

lemma rows_contacts (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (a : Finset V) : contacts G (rows p q hd) a = degreeIn G p.leaf a +
      degreeIn G (q 3) a + degreeIn G (q 1) a + degreeIn G (p.vertices 2) a := by
  rw [rows, contacts_image_left G _ _ (PawEncoding.labeling p q hd).injective]
  norm_num [weightSet]
  change degreeIn G p.leaf a + (degreeIn G (q 3) a +
    (degreeIn G (q 1) a + degreeIn G (p.vertices 2) a)) = _
  omega

lemma inside_bound (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (h : PawBlock.Pattern7 p q)
    (hleaf : ¬G.Adj p.leaf (p.vertices 2) ∧ ¬G.Adj p.leaf (p.vertices 3)) :
    contacts G (rows p q hd) (p.support ∪ q.support) ≤ 13 := by
  have hh := contacts_image_le_of_adj G graph (PawEncoding.labeling p q hd)
    (PawEncoding.labeling p q hd).injective weightSet univ
    (fun i _ j _ ↦ adj_upper p q hd h hleaf i j)
  rw [inside_weight, PawEncoding.labeling_image] at hh
  exact hh

variable [Fintype V]

theorem heavy_block {c : TriangleChain G} {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : PawBlock.Pattern7 p q) :
    ∃ a ∈ c.blocks, a ≠ b ∧ 9 ≤ contacts G (rows p q hd) a := by
  have hh := inside_bound p q hd h (c.paw_nonadjacent hcard hn p hp)
  have hinside : contacts G (rows p q hd) (c.remainder ∪ b) ≤ 15 := by
    rw [← hp, ← hq]
    omega
  exact c.exists_nine_contact_outside_core hcard hdeg hb (rows p q hd) (rows_card p q hd) hinside

end Erdos577.FirstPawSeven
