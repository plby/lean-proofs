import ErdosProblems.Erdos577.TwoExposedPositiveLabels

/-! The positive-third-row case has an explicit two-cycle factor of the paw and its block. -/

namespace Erdos577.TwoExposed

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem full_three_positive_false {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder) {a : Finset V} (ha : a ∈ c.blocks)
    (hx : degreeIn G p.leaf a = 4) (hr : 0 < degreeIn G p.center a)
    (hb : 0 < degreeIn G (p.vertices 2) a) (ht : 0 < degreeIn G (p.vertices 3) a) : False := by
  obtain ⟨q, hq, h0, h1, h2⟩ := three_positive_labels hc hcard hn p hp ha hx hr hb ht
  have hFQ : Disjoint p.support q.support := by
    rw [hp, hq]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset ha)
  have hm (i : Fin 4) : p.vertices i ∈ p.support := (mem_tupleSupport p.vertices _).mpr ⟨i, rfl⟩
  have hcross (i j : Fin 4) : p.vertices i ≠ q j := fun he ↦
    disjoint_left.mp hFQ (hm i) (he.symm ▸ (q.mem_support _).mpr ⟨j, rfl⟩)
  have hfull : ∀ u ∈ q.support, G.Adj p.leaf u :=
    (degreeIn_eq_card_iff p.leaf q.support).mp (by rw [hq, hx, (c.property.blocks_quad a ha).card])
  have hfirst : QuadOn G {p.leaf, p.center, q 0, q 3} := QuadOn.of_vertices
    (hcross 0 0) (hcross 1 3) p.pendant h0 (q.adjacent 3).symm
    (hfull (q 3) ((q.mem_support _).mpr ⟨3, rfl⟩)).symm
  have hsecond : QuadOn G {p.vertices 2, q 1, q 2, p.vertices 3} := QuadOn.of_vertices
    (hcross 2 2) (hcross 3 1).symm h1 (q.adjacent 1) h2.symm p.edge23.symm
  have hxr : Disjoint ({p.leaf, p.center} : Finset V) q.support :=
    hFQ.mono_left (insert_subset (hm 0) (singleton_subset_iff.mpr (hm 1)))
  have hbc : Disjoint ({p.vertices 2, p.vertices 3} : Finset V) q.support :=
    hFQ.mono_left (insert_subset (hm 2) (singleton_subset_iff.mpr (hm 3)))
  have hdis : Disjoint ({p.leaf, p.center} : Finset V) {p.vertices 2, p.vertices 3} := by
    simp only [disjoint_insert_left, disjoint_singleton_left, mem_insert, mem_singleton,
      Paw.leaf, Paw.center, p.vertices.injective.eq_iff, not_or]
    decide
  obtain ⟨parts⟩ := TwoCore.crossing_partition q p.leaf p.center (p.vertices 2) (p.vertices 3)
    hxr hbc hdis hfirst hsecond
  have he : insert p.leaf ({p.vertices 2, p.vertices 3, p.center} ∪ q.support) =
      c.remainder ∪ ({a} : Finset (Finset V)).biUnion id := by
    simp only [singleton_biUnion, id_eq, ← hp, ← hq, p.support_eq, Paw.triangle,
      insert_union, singleton_union]
    change insert p.leaf
        (insert (p.vertices 2) (insert (p.vertices 3) (insert p.center q.support))) =
      insert p.leaf (insert p.center (insert (p.vertices 2) (insert (p.vertices 3) q.support)))
    rw [insert_comm (p.vertices 3) p.center, insert_comm (p.vertices 2) p.center]
  exact hn (c.complementPartition.hasPacking_of_selected_factor hcard {a}
    (singleton_subset_iff.mpr ha) (he ▸ parts))

end Erdos577.TwoExposed
