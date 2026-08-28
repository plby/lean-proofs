import ErdosProblems.Erdos577.WeightedThirteenMissedTables
import ErdosProblems.Erdos577.WeightedThirteenDenseConsequences
import ErdosProblems.Erdos577.ThreeContactScore
import ErdosProblems.Erdos577.SelectedMatchingScore

/-! Each forbidden contact at the missed vertex yields an actual two-edge score gain. -/

namespace Erdos577.WeightedThirteen.ThirdModel.MissedTable

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} {second : Bool}

def parts (f : (graph second).Copy G) (tag : Fin 4) :
    BlockPartition G (((firstBlock second tag).image f ∪ (secondBlock second tag).image f) ∪
      (thirdBlock second).image f) :=
  ((BlockPartition.single ((first_quad second tag).image f)).union
    (BlockPartition.single ((second_quad second tag).image f))
    ((disjoint_image f.injective).mpr (first_second_disjoint second tag))).union
    (BlockPartition.single ((third_quad second).image f)) (by
      rw [← image_union]
      exact (disjoint_image (show Function.Injective (f : Fin 16 → V) from f.injective)).mpr
        (third_disjoint second tag))

lemma covered_subset (f : (graph second).Copy G) (tag : Fin 4) :
    ((firstBlock second tag).image f ∪ (secondBlock second tag).image f) ∪
      (thirdBlock second).image f ⊆ univ.image f := by
  rw [← image_union, ← image_union]
  exact image_subset_image (subset_univ _)

lemma matching_complement (f : (graph second).Copy G) (tag : Fin 4)
    (hevent : G.Adj (f 15) (f (eventIndex second tag))) :
    (matching f tag hevent).support = univ.image f \
      (((firstBlock second tag).image f ∪ (secondBlock second tag).image f) ∪
        (thirdBlock second).image f) := by
  have hinj : Function.Injective (f : Fin 16 → V) := f.injective
  rw [matching_support, ← image_union, ← image_union, ← image_sdiff _ _ hinj, complement]

variable [DecidableRel G.Adj]

lemma parts_score (f : (graph second).Copy G) (tag : Fin 4) :
    (parts f tag).weightSum (edgeCount G) = 12 + edgeCount G ((thirdBlock second).image f) := by
  simp only [parts, BlockPartition.weightSum_union, BlockPartition.weightSum_single,
    first_image_score, second_image_score]

omit [DecidableRel G.Adj] in
lemma third_image (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (v : Quadrilateral G) (hv : Disjoint (p.support ∪ q.support) v.support)
    (w : Quadrilateral G) (hw : Disjoint ((p.support ∪ q.support) ∪ v.support) w.support)
    (second : Bool) :
    (thirdBlock second).image (labeling p q hd v hv w hw) =
      insert (q (lowIndex second)) (w.support.erase (w 3)) := by
  have hinj : Function.Injective (w : Fin 4 → V) := w.injective
  rw [Quadrilateral.support, ← image_erase hinj,
    show univ.erase (3 : Fin 4) = {0, 1, 2} by decide]
  cases second <;> simp only [thirdBlock, low, image_insert, image_singleton] <;> rfl

lemma third_image_score (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (h : WeightedPawBlock.Pattern13 p q) (v : Quadrilateral G)
    (hv : Disjoint (p.support ∪ q.support) v.support)
    (hcl : G.IsNClique 4 v.support) (hrows : DenseRows p q v)
    (w : Quadrilateral G) (hw : Disjoint ((p.support ∪ q.support) ∪ v.support) w.support)
    (hdiag : G.Adj (q 0) (q 2)) (second : Bool)
    (hrow : ∀ j : Fin 4, G.Adj (q (lowIndex second)) (w j) ↔ j ≠ 3)
    (hwdiag : ¬G.Adj (w 1) (w 3)) :
    edgeCount G ((thirdBlock second).image (copy p q hd h v hv hcl hrows w hw hdiag second hrow)) =
      edgeCount G w.support + 1 := by
  change edgeCount G ((thirdBlock second).image (labeling p q hd v hv w hw)) = _
  rw [third_image]
  apply w.three_contact_replace_score _ _ hrow hwdiag
  intro hz
  exact disjoint_left.mp hw
    (mem_union_left _ (mem_union_right _ ((q.mem_support _).mpr ⟨lowIndex second, rfl⟩))) hz

end Erdos577.WeightedThirteen.ThirdModel.MissedTable

namespace Erdos577.WeightedThirteen

open Finset ThirdModel

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem no_missed_contact {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern13 p q)
    {a : Finset V} (ha : a ∈ c.blocks) (hab : a ≠ b) (v : Quadrilateral G) (hv : v.support = a)
    (hdis : Disjoint (p.support ∪ q.support) v.support)
    (hcl : G.IsNClique 4 v.support) (hrows : DenseRows p q v)
    {t : Finset V} (ht : t ∈ c.blocks) (htb : t ≠ b) (hta : t ≠ a)
    (w : Quadrilateral G) (hw : w.support = t)
    (hdt : Disjoint ((p.support ∪ q.support) ∪ v.support) w.support)
    (hdiag : G.Adj (q 0) (q 2)) (second : Bool)
    (hrow : ∀ j : Fin 4, G.Adj (q (lowIndex second)) (w j) ↔ j ≠ 3)
    (hwdiag : ¬G.Adj (w 1) (w 3)) (tag : Fin 4) :
    ¬G.Adj (w 3) (labeling p q hd v hdis w hdt (MissedTable.eventIndex second tag)) := by
  intro hbad
  let f := copy p q hd h v hdis hcl hrows w hdt hdiag second hrow
  have hevent : G.Adj (f 15) (f (MissedTable.eventIndex second tag)) := hbad
  have hbs : ({b, a, t} : Finset (Finset V)) ⊆ c.blocks := by
    intro z hz
    rcases mem_insert.mp hz with rfl | hz
    · exact hb
    · rcases mem_insert.mp hz with rfl | hz
      · exact ha
      · exact mem_singleton.mp hz ▸ ht
  have he : univ.image f = c.remainder ∪ ({b, a, t} : Finset (Finset V)).biUnion id := by
    rw [show univ.image f = ((p.support ∪ q.support) ∪ v.support) ∪ w.support from
      labeling_image p q hd v hdis w hdt]
    simp only [hp, hq, hv, hw, biUnion_insert, singleton_biUnion, id_eq, union_assoc]
  have hsub := MissedTable.covered_subset f tag
  rw [he] at hsub
  have hmatch := MissedTable.matching_complement f tag hevent
  rw [he] at hmatch
  have hbound := hc.selected_matching_edges_le hcard hdeg hn {b, a, t} hbs
    (MissedTable.parts f tag) hsub (MissedTable.matching f tag hevent) hmatch
  have hq5 : edgeCount G b = 5 := by
    rw [← hq, q.edgeCount_eq, if_pos hdiag, if_neg h.1]
  have hv6 : edgeCount G a = 6 := by
    rw [← hv, edgeCount_clique hcl.isClique, hcl.card_eq]
    decide +kernel
  have hold : (c.complementPartition.select {b, a, t} hbs).weightSum (edgeCount G) =
      11 + edgeCount G t := by
    simp [BlockPartition.weightSum, BlockPartition.select, hab.symm, htb.symm, hta.symm, hq5, hv6]
    omega
  have hnew := MissedTable.parts_score f tag
  have hthird := MissedTable.third_image_score p q hd h v hdis hcl hrows w hdt hdiag second
    hrow hwdiag
  change edgeCount G ((MissedTable.thirdBlock second).image f) = edgeCount G w.support + 1 at hthird
  rw [hw] at hthird
  omega

end Erdos577.WeightedThirteen
