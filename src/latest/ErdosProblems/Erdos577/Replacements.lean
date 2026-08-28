import ErdosProblems.Erdos577.Blocks
import ErdosProblems.Erdos577.EdgeChanges

/-! Insertions into a genuine quadrilateral, with exact vertex supports. -/

namespace Erdos577

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

namespace Quadrilateral

/-- Replace one cyclic vertex by an outside vertex meeting its two cycle neighbors. -/
def replaceAt (q : Quadrilateral G) (i : Fin 4) (z : V) (hz : z ∉ q.support)
    (he : ∀ j, (SimpleGraph.cycleGraph 4).Adj i j → G.Adj z (q j)) : Quadrilateral G :=
  ofEdges (q.toEmbedding.setValue i z) (by
    have hn (j : Fin 4) : q j ≠ z := fun h ↦ hz ((q.mem_support z).mpr ⟨j, h⟩)
    intro j
    have hcycle : (SimpleGraph.cycleGraph 4).Adj j (j + 1) :=
      (cycleGraph_four_adj_iff j (j + 1)).mpr (Or.inr rfl)
    have hnext : j + 1 ≠ j := fun h ↦ (q.adjacent j).ne (congrArg q h.symm)
    by_cases hji : j = i
    · subst j
      rw [Function.Embedding.setValue_eq,
        Function.Embedding.setValue_eq_of_ne hnext (hn _)]
      exact he _ hcycle
    · by_cases hji' : j + 1 = i
      · rw [Function.Embedding.setValue_eq_of_ne hji (hn _), hji',
          Function.Embedding.setValue_eq]
        exact (he j (hji' ▸ hcycle.symm)).symm
      · rw [Function.Embedding.setValue_eq_of_ne hji (hn _),
          Function.Embedding.setValue_eq_of_ne hji' (hn _)]
        exact q.adjacent j)

lemma replaceAt_apply (q : Quadrilateral G) (i : Fin 4) (z : V) (hz : z ∉ q.support)
    (he : ∀ j, (SimpleGraph.cycleGraph 4).Adj i j → G.Adj z (q j)) :
    q.replaceAt i z hz he i = z := by
  change (q.toEmbedding.setValue i z) i = z
  exact Function.Embedding.setValue_eq _ _ _

lemma replaceAt_apply_of_ne (q : Quadrilateral G) (i : Fin 4) (z : V) (hz : z ∉ q.support)
    (he : ∀ j, (SimpleGraph.cycleGraph 4).Adj i j → G.Adj z (q j))
    {j : Fin 4} (hji : j ≠ i) : q.replaceAt i z hz he j = q j := by
  exact Function.Embedding.setValue_eq_of_ne hji
    (fun h ↦ hz ((q.mem_support z).mpr ⟨j, h⟩))

lemma replaceAt_support (q : Quadrilateral G) (i : Fin 4) (z : V) (hz : z ∉ q.support)
    (he : ∀ j, (SimpleGraph.cycleGraph 4).Adj i j → G.Adj z (q j)) :
    (q.replaceAt i z hz he).support = insert z (q.support.erase (q i)) := by
  ext v
  simp only [mem_support, mem_insert, mem_erase]
  constructor
  · rintro ⟨j, rfl⟩
    by_cases hji : j = i
    · subst j
      exact Or.inl (q.replaceAt_apply i z hz he)
    · rw [q.replaceAt_apply_of_ne i z hz he hji]
      exact Or.inr ⟨fun h ↦ hji (q.injective h), ⟨j, rfl⟩⟩
  · rintro (hvz | ⟨hvi, j, hjv⟩)
    · exact ⟨i, (q.replaceAt_apply i z hz he).trans hvz.symm⟩
    · refine ⟨j, (q.replaceAt_apply_of_ne i z hz he ?_).trans hjv⟩
      exact fun h ↦ hvi (hjv.symm.trans (congrArg q h))

lemma quad_replaceAt (q : Quadrilateral G) (i : Fin 4) (z : V) (hz : z ∉ q.support)
    (he : ∀ j, (SimpleGraph.cycleGraph 4).Adj i j → G.Adj z (q j)) :
    QuadOn G (insert z (q.support.erase (q i))) :=
  ⟨q.replaceAt i z hz he, q.replaceAt_support i z hz he⟩

end Quadrilateral

omit [DecidableEq V] in
lemma degreeIn_eq_card_iff [DecidableRel G.Adj] (z : V) (s : Finset V) :
    degreeIn G z s = s.card ↔ ∀ v ∈ s, G.Adj z v := card_filter_eq_iff

omit [DecidableEq V] in
lemma degreeIn_eq_zero_iff [DecidableRel G.Adj] (z : V) (s : Finset V) :
    degreeIn G z s = 0 ↔ ∀ v ∈ s, ¬G.Adj z v := card_filter_eq_zero_iff

lemma QuadOn.replace_of_complete {s : Finset V} (hs : QuadOn G s) {z : V}
    (hz : z ∉ s) (hrow : ∀ w ∈ s, G.Adj z w) {v : V} (hv : v ∈ s) :
    QuadOn G (insert z (s.erase v)) := by
  obtain ⟨q, rfl⟩ := hs
  obtain ⟨i, rfl⟩ := (q.mem_support v).mp hv
  exact q.quad_replaceAt i z hz (fun j _ ↦ hrow (q j) ((q.mem_support _).mpr ⟨j, rfl⟩))

lemma QuadOn.replace_of_degree_four [DecidableRel G.Adj] {s : Finset V}
    (hs : QuadOn G s) {z : V} (hz : z ∉ s) (hrow : degreeIn G z s = 4)
    {v : V} (hv : v ∈ s) : QuadOn G (insert z (s.erase v)) := by
  exact hs.replace_of_complete hz ((degreeIn_eq_card_iff z s).mp (hrow.trans hs.card.symm)) hv

/-- Three contacts suffice for every replacement in a complete four-set. -/
lemma clique_replace_of_degree_three [DecidableRel G.Adj] {s : Finset V}
    (hs : G.IsNClique 4 s) {z : V} (hz : z ∉ s) (hrow : 3 ≤ degreeIn G z s)
    {v : V} (hv : v ∈ s) : QuadOn G (insert z (s.erase v)) := by
  have htri : G.IsNClique 3 (s.erase v) := by
    refine ⟨SimpleGraph.IsClique.subset (coe_subset.mpr (erase_subset v s)) hs.isClique, ?_⟩
    rw [card_erase_of_mem hv, hs.card_eq]
  have he := degreeIn_erase_add G z v hv
  have htwo : 2 ≤ degreeIn G z (s.erase v) := by
    split_ifs at he <;> omega
  exact QuadOn.of_triangle htri (fun h ↦ hz (mem_erase.mp h).2) htwo

end Erdos577
