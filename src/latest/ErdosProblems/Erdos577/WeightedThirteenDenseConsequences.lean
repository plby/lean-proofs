import ErdosProblems.Erdos577.WeightedThirteenDenseFactors
import ErdosProblems.Erdos577.WeightedThirteenDenseHeavy
import ErdosProblems.Erdos577.WeightedThirteenAlternatePaw

/-! The actual third-block insertion prohibitions and the leaf-degree bound. -/

namespace Erdos577.WeightedThirteen

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [DecidableRel G.Adj] in
lemma no_dense_factor {c : TriangleChain G} {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    {a : Finset V} (ha : a ∈ c.blocks) (v : Quadrilateral G) (hv : v.support = a)
    {t : Finset V} (ht : t ∈ c.blocks) :
    ¬Nonempty (BlockPartition G (((p.support ∪ q.support) ∪ v.support) ∪ t)) := by
  rintro ⟨part⟩
  have hbs : ({b, a, t} : Finset (Finset V)) ⊆ c.blocks := by
    intro z hz
    rcases mem_insert.mp hz with rfl | hz
    · exact hb
    · rcases mem_insert.mp hz with rfl | hz
      · exact ha
      · exact mem_singleton.mp hz ▸ ht
  have he : c.remainder ∪ ({b, a, t} : Finset (Finset V)).biUnion id =
      ((p.support ∪ q.support) ∪ v.support) ∪ t := by
    simp only [biUnion_insert, singleton_biUnion, id_eq, hp, hq, hv, union_assoc]
  exact hn (c.complementPartition.hasPacking_of_selected_factor hcard {b, a, t} hbs
    (he.symm ▸ part))

omit [DecidableRel G.Adj] in
lemma dense_core_disjoint {c : TriangleChain G}
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    {a : Finset V} (ha : a ∈ c.blocks) (v : Quadrilateral G) (hv : v.support = a)
    {t : Finset V} (ht : t ∈ c.blocks) (htb : t ≠ b) (hta : t ≠ a) :
    Disjoint ((p.support ∪ q.support) ∪ v.support) t := by
  rw [hp, hq, hv, disjoint_union_left, disjoint_union_left]
  refine ⟨⟨?_, c.property.blocks_disjoint hb ht htb.symm⟩,
    c.property.blocks_disjoint ha ht hta.symm⟩
  apply disjoint_left.mpr
  intro u hu hut
  exact (mem_sdiff.mp (c.complementPartition.block_subset ht hut)).2 hu

omit [DecidableRel G.Adj] in
lemma no_dense_common {c : TriangleChain G} {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern13 p q)
    {a : Finset V} (ha : a ∈ c.blocks) (v : Quadrilateral G) (hv : v.support = a)
    (hdis : Disjoint (p.support ∪ q.support) v.support)
    (hcl : G.IsNClique 4 v.support) (hrows : DenseRows p q v)
    {t : Finset V} (ht : t ∈ c.blocks) (htb : t ≠ b) (hta : t ≠ a) (tag : Fin 13) :
    ¬CommonReplacement G
      (WeightedFifteen.twoBlockLabeling p q hd v hdis (DenseModel.FinalTable.triple tag 0))
      (WeightedFifteen.twoBlockLabeling p q hd v hdis (DenseModel.FinalTable.triple tag 2))
      (WeightedFifteen.twoBlockLabeling p q hd v hdis (DenseModel.FinalTable.terminal tag)) t := by
  classical
  intro hh
  let f := DenseModel.copy p q hd h v hdis hcl hrows
  have he : univ.image f = (p.support ∪ q.support) ∪ v.support :=
    WeightedFifteen.twoBlockLabeling_image p q hd v hdis
  have hdt : Disjoint (univ.image f) t := by
    rw [he]
    exact dense_core_disjoint p hp hb q hq ha v hv ht htb hta
  have hf := DenseModel.FinalTable.common_factor f tag t hdt hh
  rw [he] at hf
  exact no_dense_factor hcard hn p hp hb q hq ha v hv ht hf

omit [Fintype V] in
lemma four_contacts (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (v : Quadrilateral G) (hv : Disjoint (p.support ∪ q.support) v.support) (t : Finset V) :
    contacts G (DenseModel.FinalTable.fourSet.image
      (WeightedFifteen.twoBlockLabeling p q hd v hv)) t =
      degreeIn G (v 1) t + degreeIn G (v 2) t + degreeIn G (q 1) t + degreeIn G (q 3) t := by
  let e := WeightedFifteen.twoBlockLabeling p q hd v hv
  rw [contacts_image_left G _ e e.injective]
  norm_num [DenseModel.FinalTable.fourSet]
  change degreeIn G (v 1) t + (degreeIn G (v 2) t +
    (degreeIn G (q 1) t + degreeIn G (q 3) t)) = _
  omega

theorem dense_leaf_le_two {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern13 p q)
    {a : Finset V} (ha : a ∈ c.blocks) (v : Quadrilateral G) (hv : v.support = a)
    (hdis : Disjoint (p.support ∪ q.support) v.support)
    (hcl : G.IsNClique 4 v.support) (hrows : DenseRows p q v)
    {t : Finset V} (ht : t ∈ c.blocks) (htb : t ≠ b) (hta : t ≠ a)
    (hheavy : 13 ≤ denseWeight p q v t) : degreeIn G p.leaf t ≤ 2 := by
  by_contra! hbig
  let f := DenseModel.copy p q hd h v hdis hcl hrows
  have he : univ.image f = (p.support ∪ q.support) ∪ v.support :=
    WeightedFifteen.twoBlockLabeling_image p q hd v hdis
  have hdt : Disjoint (univ.image f) t := by
    rw [he]
    exact dense_core_disjoint p hp hb q hq ha v hv ht htb hta
  have ht4 : t.card = 4 := (c.property.blocks_quad t ht).card
  have hdx := degreeIn_le_card G p.leaf t
  rw [ht4] at hdx
  have h5 : 5 ≤ contacts G (DenseModel.FinalTable.fourSet.image f) t := by
    change 5 ≤ contacts G (DenseModel.FinalTable.fourSet.image
      (WeightedFifteen.twoBlockLabeling p q hd v hdis)) t
    rw [four_contacts]
    unfold denseWeight at hheavy
    omega
  have hrep (u : V) (hu : u ∈ t) : QuadOn G (insert (f 0) (t.erase u)) :=
    (hc.presentPaw_feasible p hp).terminal_universal_replace ht hbig hu
  have hf := DenseModel.FinalTable.factor_of_five f t hdt ht4 h5 hrep
  rw [he] at hf
  exact no_dense_factor hcard hn p hp hb q hq ha v hv ht hf

end Erdos577.WeightedThirteen
