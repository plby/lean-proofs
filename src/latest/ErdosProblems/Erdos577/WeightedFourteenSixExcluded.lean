import ErdosProblems.Erdos577.WeightedFourteenSixAlternate
import ErdosProblems.Erdos577.WeightedFifteenDenseFactors

/-! Three explicit quadrilaterals exclude case (6) at pattern (14)'s heavy block. -/

namespace Erdos577.WeightedFourteen

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

lemma six_factor_partition (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern14 p q)
    (v : Quadrilateral G) (hv : Disjoint (p.support ∪ q.support) v.support)
    (hdiag : G.Adj (v 0) (v 2)) (hrows : PawBlock.ExactRows p v ![3, 13, 7, 1])
    (hedge : G.Adj (q 3) (v 3)) :
    Nonempty (BlockPartition G ((p.support ∪ q.support) ∪ v.support)) := by
  let e := WeightedFifteen.twoBlockLabeling p q hd v hv
  have hne (i j : Fin 12) (hij : i ≠ j) : e i ≠ e j := fun he ↦ hij (e.injective he)
  let s : Finset (Fin 12) := {7, 11, 1, 2}
  let t : Finset (Fin 12) := {0, 8, 10, 9}
  let u : Finset (Fin 12) := {3, 4, 5, 6}
  have hs : QuadOn G (s.image e) := by
    simp only [s, image_insert, image_singleton]
    exact QuadOn.of_vertices (hne 7 1 (by decide)) (hne 11 2 (by decide))
      hedge ((hrows 1 3).mpr (by decide)).symm p.edge12 ((h.2.2.1 3).mpr (by decide))
  have ht : QuadOn G (t.image e) := by
    simp only [t, image_insert, image_singleton]
    exact QuadOn.of_vertices (hne 0 10 (by decide)) (hne 8 9 (by decide))
      ((hrows 0 0).mpr (by decide)) hdiag (v.adjacent 1).symm
      ((hrows 0 1).mpr (by decide)).symm
  have hu : QuadOn G (u.image e) := by
    simp only [u, image_insert, image_singleton]
    exact QuadOn.of_vertices (hne 3 5 (by decide)) (hne 4 6 (by decide))
      ((h.2.2.2 0).mpr (by decide)) (q.adjacent 0) (q.adjacent 1)
      ((h.2.2.2 2).mpr (by decide)).symm
  let part := BlockPartition.threeImages e s t u univ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) hs ht hu
  exact ⟨WeightedFifteen.twoBlockLabeling_image p q hd v hv ▸ part⟩

variable [Fintype V] [DecidableRel G.Adj]

theorem six_excluded {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern14 p q)
    {a : Finset V} (ha : a ∈ c.blocks) (hab : a ≠ b) (hheavy : 17 ≤ weight p q a)
    (v : Quadrilateral G) (hv : v.support = a) (swap : Bool)
    (h6 : PawBlock.Pattern6 (FirstPaw.normalizedPaw p swap) v) : False := by
  obtain ⟨hswap, hedge⟩ := six_alternate_contact hc hcard hdeg hn p hp hb q hq hd h ha hab
    hheavy v hv swap h6
  subst swap
  obtain ⟨hx2, hy2, _, _, hE, _⟩ := heavy_rows hc hcard hdeg hn p hp hb q hq hd h ha hab hheavy
  obtain ⟨_, _, _, hrows⟩ := six_rows hc hcard hn p hp hb q hq hd h ha hab v hv false h6 hx2 hy2 hE
  have hdis : Disjoint (p.support ∪ q.support) v.support := by
    rw [hp, hq, hv, disjoint_union_left]
    refine ⟨?_, c.property.blocks_disjoint hb ha hab.symm⟩
    apply disjoint_left.mpr
    intro w hw hwa
    exact (mem_sdiff.mp (c.complementPartition.block_subset ha hwa)).2 hw
  obtain ⟨part⟩ := six_factor_partition p q hd h v hdis h6.1.1 hrows hedge
  rw [hp, hq, hv] at part
  have hbs : ({b, a} : Finset (Finset V)) ⊆ c.blocks := by
    intro x hx
    rcases mem_insert.mp hx with rfl | hx
    · exact hb
    · exact mem_singleton.mp hx ▸ ha
  have he : c.remainder ∪ ({b, a} : Finset (Finset V)).biUnion id =
      (c.remainder ∪ b) ∪ a := by
    simp only [biUnion_insert, singleton_biUnion, id_eq, union_assoc]
  exact hn (c.complementPartition.hasPacking_of_selected_factor hcard {b, a} hbs (he.symm ▸ part))

theorem four_or_five_at_heavy {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern14 p q)
    {a : Finset V} (ha : a ∈ c.blocks) (hab : a ≠ b) (hheavy : 17 ≤ weight p q a) :
    ∃ swap : Bool, ∃ v : Quadrilateral G, v.support = a ∧
      (PawBlock.Pattern4 (FirstPaw.normalizedPaw p swap) v ∨
        PawBlock.Pattern5 (FirstPaw.normalizedPaw p swap) v) := by
  obtain ⟨hx2, _, _, _, hE, _⟩ := heavy_rows hc hcard hdeg hn p hp hb q hq hd h ha hab hheavy
  obtain ⟨v, hv⟩ := c.property.blocks_quad a ha
  have hclass := hc.first_paw_classification hcard hdeg hn p hp ha v hv
    (by rw [hv]; exact hE) (by rw [hv]; omega)
  obtain ⟨swap, w, hws, hcase⟩ := hclass.leaf_two p v (by rw [hv]; exact hx2)
  refine ⟨swap, w, hws.trans hv, ?_⟩
  rcases hcase with h4 | h5 | h6
  · exact Or.inl h4
  · exact Or.inr h5
  · exact False.elim (six_excluded hc hcard hdeg hn p hp hb q hq hd h ha hab hheavy
      w (hws.trans hv) swap h6)

end Erdos577.WeightedFourteen
