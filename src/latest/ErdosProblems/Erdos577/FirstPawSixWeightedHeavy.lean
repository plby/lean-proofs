import ErdosProblems.Erdos577.FirstPawSixWeightedModel
import ErdosProblems.Erdos577.ExactCopyCounts

/-! Case24 has exact inside weight twenty and an outside block of weight at least thirteen. -/

namespace Erdos577.FirstPawSix.WeightedCase

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma inside_exact (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (hdiag : PawBlock.OnlyFirst q) (hrows : PawBlock.ExactRows p q (caseRows 2))
    (hleaf : ¬G.Adj p.leaf (p.vertices 2) ∧ ¬G.Adj p.leaf (p.vertices 3)) :
    FirstPawFour.weight p q (p.support ∪ q.support) = 20 := by
  let e := PawEncoding.labeling p q hd
  have he (second : Bool) := contacts_image_eq_of_adj G graph e e.injective
    (FirstPawFour.weightSet second) univ
    (fun i _ j _ ↦ CaseModel.adj_iff p q hd hdiag 2 hrows hleaf i j)
  have hh := congrArg₂ (fun x y : ℕ ↦ x + y) (he false) (he true)
  rw [PawEncoding.labeling_image, inside_weight] at hh
  rw [FirstPawFour.weight_eq p q hd]
  exact hh

lemma other_contacts (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (a : Finset V) : contacts G ((vertexSet.erase 0).image (PawEncoding.labeling p q hd)) a =
    degreeIn G (p.vertices 2) a + degreeIn G (p.vertices 3) a +
      degreeIn G (q 1) a + degreeIn G (q 3) a := by
  rw [contacts_image_left G _ _ (PawEncoding.labeling p q hd).injective]
  norm_num [vertexSet]
  change degreeIn G (p.vertices 2) a + (degreeIn G (p.vertices 3) a +
    (degreeIn G (q 1) a + degreeIn G (q 3) a)) = _
  omega

variable [Fintype V]

theorem heavy_block {c : TriangleChain G} {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (hdiag : PawBlock.OnlyFirst q)
    (hrows : PawBlock.ExactRows p q (caseRows 2)) :
    ∃ a ∈ c.blocks, a ≠ b ∧ 13 ≤ FirstPawFour.weight p q a := by
  let e := PawEncoding.labeling p q hd
  have h3 (second : Bool) : ((FirstPawFour.weightSet second).image e).card = 3 := by
    rw [card_image_of_injective _ e.injective, FirstPawFour.weightSet_card]
  have hinside : contacts G ((FirstPawFour.weightSet false).image e) (c.remainder ∪ b) +
      contacts G ((FirstPawFour.weightSet true).image e) (c.remainder ∪ b) ≤ 22 := by
    rw [← FirstPawFour.weight_eq p q hd, ← hp, ← hq,
      inside_exact p q hd hdiag hrows (c.paw_nonadjacent hcard hn p hp)]
    decide
  obtain ⟨a, ha, hab, hh⟩ := c.exists_paired_thirteen_outside_one hcard hdeg hb
    ((FirstPawFour.weightSet false).image e) ((FirstPawFour.weightSet true).image e)
    (h3 false) (h3 true) hinside
  rw [← FirstPawFour.weight_eq p q hd] at hh
  exact ⟨a, ha, hab, hh⟩

end Erdos577.FirstPawSix.WeightedCase
