import ErdosProblems.Erdos577.FirstPawFourUpper
import ErdosProblems.Erdos577.OutsideOnePairs
import ErdosProblems.Erdos577.PawInduced

/-! The exact repeated-leaf degree average supplies the outside block in pattern (4). -/

namespace Erdos577.FirstPawFour

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

def weight (p : Paw G) (q : Quadrilateral G) (a : Finset V) : ℕ :=
  2 * degreeIn G p.leaf a + degreeIn G (p.vertices 2) a + degreeIn G (p.vertices 3) a +
    degreeIn G (q 1) a + degreeIn G (q 3) a

lemma weight_eq (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (a : Finset V) : weight p q a =
    contacts G ((weightSet false).image (PawEncoding.labeling p q hd)) a +
      contacts G ((weightSet true).image (PawEncoding.labeling p q hd)) a := by
  let e := PawEncoding.labeling p q hd
  rw [contacts_image_left G _ e e.injective, contacts_image_left G _ e e.injective]
  norm_num [weightSet]
  change weight p q a = degreeIn G p.leaf a +
    (degreeIn G (p.vertices 2) a + degreeIn G (p.vertices 3) a) +
    (degreeIn G p.leaf a + (degreeIn G (q 1) a + degreeIn G (q 3) a))
  unfold weight
  omega

lemma inside_bound (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (h : PawBlock.Pattern4 p q)
    (hleaf : ¬G.Adj p.leaf (p.vertices 2) ∧ ¬G.Adj p.leaf (p.vertices 3)) :
    weight p q (p.support ∪ q.support) ≤ 22 := by
  let e := PawEncoding.labeling p q hd
  have hl (second : Bool) := contacts_image_le_of_adj G upperGraph e e.injective
    (weightSet second) univ (fun i _ j _ ↦ adj_upper p q hd h hleaf i j)
  have he := Nat.add_le_add (hl false) (hl true)
  rw [inside_weight, PawEncoding.labeling_image] at he
  rw [weight_eq p q hd]
  exact he

variable [Fintype V]

theorem heavy_block {c : TriangleChain G} {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : PawBlock.Pattern4 p q) :
    ∃ a ∈ c.blocks, a ≠ b ∧ 13 ≤ weight p q a := by
  let e := PawEncoding.labeling p q hd
  have h3 (second : Bool) : ((weightSet second).image e).card = 3 := by
    rw [card_image_of_injective _ e.injective, weightSet_card]
  have hinside : contacts G ((weightSet false).image e) (c.remainder ∪ b) +
      contacts G ((weightSet true).image e) (c.remainder ∪ b) ≤ 22 := by
    rw [← weight_eq p q hd, ← hp, ← hq]
    exact inside_bound p q hd h (c.paw_nonadjacent hcard hn p hp)
  obtain ⟨a, ha, hab, hh⟩ := c.exists_paired_thirteen_outside_one hcard hdeg hb
    ((weightSet false).image e) ((weightSet true).image e) (h3 false) (h3 true) hinside
  rw [← weight_eq p q hd] at hh
  exact ⟨a, ha, hab, hh⟩

end Erdos577.FirstPawFour
