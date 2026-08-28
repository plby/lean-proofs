import ErdosProblems.Erdos577.WeightedThirteenCommonTables

/-! The common-neighbor exchange contradicts the second maximum when edge scores tie. -/

namespace Erdos577.WeightedThirteen

open Finset ThirdModel

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem no_high_common {c : TriangleChain G} (hc : c.Feasible)
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
    ¬(G.Adj (labeling p q hd v hdis w hdt (CommonTable.commonIndex tag)) p.leaf ∧
      G.Adj (labeling p q hd v hdis w hdt (CommonTable.commonIndex tag))
        (labeling p q hd v hdis w hdt (CommonTable.newIndex tag))) := by
  intro hbad
  let f := copy p q hd h v hdis hcl hrows w hdt hdiag second hrow
  have hx : G.Adj (f (CommonTable.commonIndex tag)) (f 0) := hbad.1
  have hy : G.Adj (f (CommonTable.commonIndex tag)) (f (CommonTable.newIndex tag)) := hbad.2
  let part := CommonTable.parts f tag hx hy
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
  have hsub := CommonTable.covered_subset f tag
  rw [he] at hsub
  have hrem := CommonTable.remainder_image f tag
  rw [he] at hrem
  have hcard := CommonTable.remainder_image_card f tag
  have htri := (CommonTable.remainder_triangle second tag).image f
  rw [hrem] at hcard htri
  have hbound := hc.selected_edges_le {b, a, t} hbs part hsub hcard htri
  have hq5 : edgeCount G b = 5 := by
    rw [← hq, q.edgeCount_eq, if_pos hdiag, if_neg h.1]
  have hv6 : edgeCount G a = 6 := by
    rw [← hv, edgeCount_clique hcl.isClique, hcl.card_eq]
    decide +kernel
  have hw5 : edgeCount G t ≤ 5 := by
    rw [← hw, w.edgeCount_eq, if_neg hwdiag]
    split <;> omega
  have hold : (c.complementPartition.select {b, a, t} hbs).weightSum (edgeCount G) =
      11 + edgeCount G t := by
    simp [BlockPartition.weightSum, BlockPartition.select, hab.symm, htb.symm, hta.symm, hq5, hv6]
    omega
  have hnew : 16 ≤ part.weightSum (edgeCount G) := CommonTable.edges_ge_sixteen f tag hx hy
  have heq : part.weightSum (edgeCount G) =
      (c.complementPartition.select {b, a, t} hbs).weightSum (edgeCount G) := by omega
  have hcomplete := hc.selected_complete_le {b, a, t} hbs part hsub hcard htri heq
  have ht6 : edgeCount G t ≠ 6 := by omega
  have holdc : (c.complementPartition.select {b, a, t} hbs).weightSum
      (fun s ↦ if edgeCount G s = 6 then 1 else 0) = 1 := by
    simp only [BlockPartition.weightSum, BlockPartition.select]
    rw [sum_insert (by simp [hab.symm, htb.symm]), sum_insert (by simp [hta.symm]), sum_singleton]
    simp [hq5, hv6, ht6]
  have hnewc : 2 ≤ part.weightSum (fun s ↦ if edgeCount G s = 6 then 1 else 0) :=
    CommonTable.complete_ge_two f tag hx hy
  omega

end Erdos577.WeightedThirteen
