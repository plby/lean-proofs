import ErdosProblems.Erdos577.FirstPawSixSmallModel
import ErdosProblems.Erdos577.OutsideCoreCount
import ErdosProblems.Erdos577.UpperCounts
import ErdosProblems.Erdos577.PawInduced

/-! An outside block has at least nine contacts from the four distinguished rows in (22)/(23). -/

namespace Erdos577.FirstPawSix.SmallCases

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

def rows (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support) : Finset V :=
  weightSet.image (PawEncoding.labeling p q hd)

omit [DecidableRel G.Adj] in
lemma rows_card (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support) :
    (rows p q hd).card = 4 := by
  rw [rows, card_image_of_injective _ (PawEncoding.labeling p q hd).injective, weightSet_card]

lemma rows_contacts (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (a : Finset V) : contacts G (rows p q hd) a = degreeIn G (q 3) a +
      degreeIn G p.leaf a + degreeIn G (q 1) a + degreeIn G (p.vertices 3) a := by
  rw [rows, contacts_image_left G _ _ (PawEncoding.labeling p q hd).injective]
  norm_num [weightSet]
  change degreeIn G (q 3) a + (degreeIn G p.leaf a +
    (degreeIn G (q 1) a + degreeIn G (p.vertices 3) a)) = _
  omega

lemma inside_bound (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (hdiag : PawBlock.OnlyFirst q) (variant : Bool)
    (hrows : PawBlock.ExactRows p q (caseRows (caseTag variant)))
    (hleaf : ¬G.Adj p.leaf (p.vertices 2) ∧ ¬G.Adj p.leaf (p.vertices 3)) :
    contacts G (rows p q hd) (p.support ∪ q.support) ≤ 14 := by
  have hh := contacts_image_le_of_adj G (graph variant) (PawEncoding.labeling p q hd)
    (PawEncoding.labeling p q hd).injective weightSet univ
    (fun i _ j _ ↦ CaseModel.adj_upper p q hd hdiag _ hrows hleaf i j)
  rw [PawEncoding.labeling_image] at hh
  exact hh.trans (inside_weight variant)

variable [Fintype V]

theorem heavy_block {c : TriangleChain G} {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (hdiag : PawBlock.OnlyFirst q) (variant : Bool)
    (hrows : PawBlock.ExactRows p q (caseRows (caseTag variant))) :
    ∃ a ∈ c.blocks, a ≠ b ∧ 9 ≤ contacts G (rows p q hd) a := by
  have hh := inside_bound p q hd hdiag variant hrows (c.paw_nonadjacent hcard hn p hp)
  have hi : contacts G (rows p q hd) (c.remainder ∪ b) ≤ 15 := by rw [← hp, ← hq]; omega
  exact c.exists_nine_contact_outside_core hcard hdeg hb (rows p q hd) (rows_card p q hd) hi

end Erdos577.FirstPawSix.SmallCases
