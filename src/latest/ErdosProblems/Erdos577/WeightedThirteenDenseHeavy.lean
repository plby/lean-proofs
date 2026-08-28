import ErdosProblems.Erdos577.WeightedThirteenDenseModel
import ErdosProblems.Erdos577.OutsideSelectedPairs

/-! The actual repeated-leaf inside weight31 forces a third block with weight at least13. -/

namespace Erdos577.WeightedThirteen

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

def denseWeight (p : Paw G) (q v : Quadrilateral G) (a : Finset V) : ℕ :=
  2 * degreeIn G p.leaf a + degreeIn G (v 1) a + degreeIn G (v 2) a +
    degreeIn G (q 1) a + degreeIn G (q 3) a

lemma denseWeight_eq (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (v : Quadrilateral G) (hv : Disjoint (p.support ∪ q.support) v.support) (a : Finset V) :
    denseWeight p q v a =
      contacts G ((DenseModel.weightSet false).image
        (WeightedFifteen.twoBlockLabeling p q hd v hv)) a +
      contacts G ((DenseModel.weightSet true).image
        (WeightedFifteen.twoBlockLabeling p q hd v hv)) a := by
  let e := WeightedFifteen.twoBlockLabeling p q hd v hv
  unfold denseWeight
  rw [contacts_image_left G _ e e.injective, contacts_image_left G _ e e.injective]
  norm_num [DenseModel.weightSet]
  change 2 * degreeIn G p.leaf a + degreeIn G (v 1) a + degreeIn G (v 2) a +
    degreeIn G (q 1) a + degreeIn G (q 3) a =
      degreeIn G p.leaf a + (degreeIn G (v 1) a + degreeIn G (v 2) a) +
        (degreeIn G p.leaf a + (degreeIn G (q 1) a + degreeIn G (q 3) a))
  omega

lemma dense_inside_bound (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (h : WeightedPawBlock.Pattern13 p q) (v : Quadrilateral G)
    (hv : Disjoint (p.support ∪ q.support) v.support) (hrows : DenseRows p q v)
    (hleaf : ¬G.Adj p.leaf (p.vertices 2) ∧ ¬G.Adj p.leaf (p.vertices 3))
    (hcenter : ¬G.Adj p.center (q 1) ∧ ¬G.Adj p.center (q 3)) :
    denseWeight p q v ((p.support ∪ q.support) ∪ v.support) ≤ 31 := by
  let e := WeightedFifteen.twoBlockLabeling p q hd v hv
  have hl (second : Bool) := contacts_image_le_of_adj G DenseModel.upperGraph e e.injective
    (DenseModel.weightSet second) univ
      (fun i _ j _ ↦ DenseModel.adj_upper p q hd h v hv hrows hleaf hcenter i j)
  have he := Nat.add_le_add (hl false) (hl true)
  rw [DenseModel.inside_weight, WeightedFifteen.twoBlockLabeling_image] at he
  rw [denseWeight_eq p q hd v hv]
  exact he

variable [Fintype V]

theorem dense_heavy_block {c : TriangleChain G} {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern13 p q)
    {a : Finset V} (ha : a ∈ c.blocks) (hab : a ≠ b) (v : Quadrilateral G) (hv : v.support = a)
    (hrows : DenseRows p q v) :
    ∃ t ∈ c.blocks, t ≠ b ∧ t ≠ a ∧ 13 ≤ denseWeight p q v t := by
  have hdis : Disjoint (p.support ∪ q.support) v.support := by
    rw [hp, hq, hv, disjoint_union_left]
    refine ⟨?_, c.property.blocks_disjoint hb ha hab.symm⟩
    apply disjoint_left.mpr
    intro w hw hwa
    exact (mem_sdiff.mp (c.complementPartition.block_subset ha hwa)).2 hw
  let e := WeightedFifteen.twoBlockLabeling p q hd v hdis
  have hbs : ({b, a} : Finset (Finset V)) ⊆ c.blocks := by
    intro x hx
    rcases mem_insert.mp hx with rfl | hx
    · exact hb
    · exact mem_singleton.mp hx ▸ ha
  have h2 : ({b, a} : Finset (Finset V)).card = 2 := by simp [hab.symm]
  have he : c.remainder ∪ ({b, a} : Finset (Finset V)).biUnion id =
      (p.support ∪ q.support) ∪ v.support := by
    simp only [biUnion_insert, singleton_biUnion, id_eq, hp, hq, hv, union_assoc]
  have h3 (second : Bool) : ((DenseModel.weightSet second).image e).card = 3 := by
    rw [card_image_of_injective _ e.injective, DenseModel.weightSet_card]
  have hinside : contacts G ((DenseModel.weightSet false).image e)
      (c.remainder ∪ ({b, a} : Finset (Finset V)).biUnion id) +
      contacts G ((DenseModel.weightSet true).image e)
        (c.remainder ∪ ({b, a} : Finset (Finset V)).biUnion id) ≤ 31 := by
    rw [he, ← denseWeight_eq p q hd v hdis]
    exact dense_inside_bound p q hd h v hdis hrows (c.paw_nonadjacent hcard hn p hp)
      (center_absent p q hd h (by rw [hp, hq]; exact c.no_local_factor hcard hn hb))
  obtain ⟨t, ht, hnt, hh⟩ := c.exists_paired_thirteen_outside_two hcard hdeg {b, a} hbs h2
    ((DenseModel.weightSet false).image e) ((DenseModel.weightSet true).image e)
    (h3 false) (h3 true) hinside
  rw [← denseWeight_eq p q hd v hdis] at hh
  exact ⟨t, ht, fun ht ↦ hnt (mem_insert.mpr (Or.inl ht)),
    fun ht ↦ hnt (mem_insert.mpr (Or.inr (mem_singleton.mpr ht))), hh⟩

end Erdos577.WeightedThirteen
