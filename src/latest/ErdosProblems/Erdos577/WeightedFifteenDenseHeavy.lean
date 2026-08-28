import ErdosProblems.Erdos577.WeightedFifteenDenseModel
import ErdosProblems.Erdos577.OutsideSelectedCount

/-! The third block has at least thirteen contacts from the specified six vertices. -/

namespace Erdos577.WeightedFifteen

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma six_contacts (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (h : WeightedPawBlock.Pattern15 p q) (v : Quadrilateral G)
    (hv : Disjoint (p.support ∪ q.support) v.support) (a : Finset V) :
    contacts G (DenseModel.sixSet.image (twoBlockLabeling p q hd v hv)) a =
      contacts G (path true p q hd h).support a + degreeIn G (q 3) a + degreeIn G (v 0) a := by
  let e := twoBlockLabeling p q hd v hv
  have hinj : Function.Injective (e : Fin 12 → V) := e.injective
  let s : Finset (Fin 12) := {5, 3, 1, 0}
  have hs : s.image e = (path true p q hd h).support := by
    rw [FourPath.support_eq]
    simp only [s, image_insert, image_singleton]
    rfl
  have hset : DenseModel.sixSet = (s ∪ {7}) ∪ {8} := by decide +kernel
  have hd1 : Disjoint (s.image e) (({7} : Finset (Fin 12)).image e) := by
    rw [disjoint_image hinj]
    decide +kernel
  have hd2 : Disjoint ((s ∪ {7}).image e) (({8} : Finset (Fin 12)).image e) := by
    rw [disjoint_image hinj]
    decide +kernel
  change contacts G (DenseModel.sixSet.image e) a = _
  rw [hset, image_union, contacts_union_left G hd2, image_union, contacts_union_left G hd1,
    hs, image_singleton, image_singleton, contacts_singleton_left, contacts_singleton_left]
  rfl

lemma six_inside_bound (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (h : WeightedPawBlock.Pattern15 p q) (v : Quadrilateral G)
    (hv : Disjoint (p.support ∪ q.support) v.support) (hrows : DenseRows p q v)
    (hleaf : ¬G.Adj p.leaf (p.vertices 2) ∧ ¬G.Adj p.leaf (p.vertices 3))
    (hcenter : ∀ j : Fin 4, j ≠ 2 → ¬G.Adj p.center (q j)) :
    contacts G (DenseModel.sixSet.image (twoBlockLabeling p q hd v hv))
      ((p.support ∪ q.support) ∪ v.support) ≤ 32 := by
  let e := twoBlockLabeling p q hd v hv
  have hl := contacts_image_le_of_adj G DenseModel.upperGraph e e.injective
    DenseModel.sixSet univ
      (fun i _ j _ ↦ DenseModel.adj_upper p q hd h v hv hrows hleaf hcenter i j)
  change contacts G (DenseModel.sixSet.image e)
    (univ.image (twoBlockLabeling p q hd v hv)) ≤ _ at hl
  rw [twoBlockLabeling_image, DenseModel.six_inside] at hl
  exact hl

variable [Fintype V]

theorem dense_heavy_block {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern15 p q)
    {a : Finset V} (ha : a ∈ c.blocks) (hab : a ≠ b) (v : Quadrilateral G) (hv : v.support = a)
    (hrows : DenseRows p q v) :
    ∃ t ∈ c.blocks, t ≠ b ∧ t ≠ a ∧
      13 ≤ contacts G (path true p q hd h).support t + degreeIn G (q 3) t + degreeIn G (v 0) t := by
  have hdis : Disjoint (p.support ∪ q.support) v.support := by
    rw [hp, hq, hv, disjoint_union_left]
    refine ⟨?_, c.property.blocks_disjoint hb ha hab.symm⟩
    apply disjoint_left.mpr
    intro w hw hwa
    exact (mem_sdiff.mp (c.complementPartition.block_subset ha hwa)).2 hw
  let e := twoBlockLabeling p q hd v hdis
  have hbs : ({b, a} : Finset (Finset V)) ⊆ c.blocks := by
    intro x hx
    rcases mem_insert.mp hx with rfl | hx
    · exact hb
    · exact mem_singleton.mp hx ▸ ha
  have h2 : ({b, a} : Finset (Finset V)).card = 2 := by simp [hab.symm]
  have he : c.remainder ∪ ({b, a} : Finset (Finset V)).biUnion id =
      (p.support ∪ q.support) ∪ v.support := by
    simp only [biUnion_insert, singleton_biUnion, id_eq, hp, hq, hv, union_assoc]
  have h6 : (DenseModel.sixSet.image e).card = 6 := by
    rw [card_image_of_injective _ e.injective, DenseModel.sixSet_card]
  have hinside : contacts G (DenseModel.sixSet.image e)
      (c.remainder ∪ ({b, a} : Finset (Finset V)).biUnion id) ≤ 32 := by
    rw [he]
    exact six_inside_bound p q hd h v hdis hrows (c.paw_nonadjacent hcard hn p hp)
      (center_absent hc hcard hn p hp hb q hq hd h)
  obtain ⟨t, ht, hnt, hh⟩ := c.exists_thirteen_outside_two hcard hdeg {b, a} hbs h2
    (DenseModel.sixSet.image e) h6 hinside
  rw [six_contacts p q hd h v hdis] at hh
  exact ⟨t, ht, fun ht ↦ hnt (mem_insert.mpr (Or.inl ht)),
    fun ht ↦ hnt (mem_insert.mpr (Or.inr (mem_singleton.mpr ht))), hh⟩

theorem dense_high_terminal {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern15 p q)
    (z : V) {t : Finset V} (ht : t ∈ c.blocks) (htb : t ≠ b)
    (h13 : 13 ≤ contacts G (path true p q hd h).support t + degreeIn G (q 3) t + degreeIn G z t) :
    3 ≤ degreeIn G (q 3) t ∨ 3 ≤ degreeIn G z t := by
  by_cases h9 : 9 ≤ contacts G (path true p q hd h).support t
  · have h10 := (fourth_bounds hc hcard hdeg hn p hp hb q hq hd h ht htb h9).2.2.1
    exact Or.inr (by omega)
  · omega

end Erdos577.WeightedFifteen
