import Arxiv.Arxiv2411_18291.DecompositionGluing

/-!
# Intersections and edge disjointness of cliques

For positive rank, two cliques sharing exactly one edge intersect in
exactly that edge's vertices. Distinct cliques of a true decomposition
are edge-disjoint and have fewer than `r` common vertices.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [Fintype V] [DecidableEq V] {q k r : ℕ}

theorem cliqueEdges_inter_singleton_of_vertices (P : Block V q) (Q : Block V k)
    (e : Block V r) (hPQ : P.val ∩ Q.val = e.val) :
    cliqueEdges r P ∩ cliqueEdges r Q = {e} := by
  ext f
  simp only [mem_inter, mem_cliqueEdges, mem_singleton]
  constructor
  · intro hf
    have hfe : f.val ⊆ e.val := hPQ ▸ subset_inter hf.1 hf.2
    exact Subtype.ext (eq_of_subset_of_card_le hfe (by rw [e.property, f.property]))
  · intro hfe
    subst f
    have he : e.val ⊆ P.val ∩ Q.val := hPQ ▸ Subset.refl _
    exact ⟨he.trans inter_subset_left, he.trans inter_subset_right⟩

theorem vertices_inter_eq_of_cliqueEdges_singleton (hr : 0 < r)
    (P : Block V q) (Q : Block V k) (e : Block V r)
    (hPQ : cliqueEdges r P ∩ cliqueEdges r Q = {e}) : P.val ∩ Q.val = e.val := by
  have hePQ : e ∈ cliqueEdges r P ∩ cliqueEdges r Q := hPQ ▸ mem_singleton_self e
  have heP := (mem_cliqueEdges e P).mp (mem_inter.mp hePQ).1
  have heQ := (mem_cliqueEdges e Q).mp (mem_inter.mp hePQ).2
  have heSub : e.val ⊆ P.val ∩ Q.val := subset_inter heP heQ
  apply subset_antisymm _ heSub
  intro v hv
  have hcard : r ≤ (P.val ∩ Q.val).card := by
    simpa only [e.property] using card_le_card heSub
  obtain ⟨s, hvs, hs, hsr⟩ := exists_subsuperset_card_eq (singleton_subset_iff.mpr hv)
    (by rw [card_singleton]; omega) hcard
  have hsPQ : (⟨s, hsr⟩ : Block V r) ∈ cliqueEdges r P ∩ cliqueEdges r Q :=
    mem_inter.mpr ⟨(mem_cliqueEdges _ _).mpr (hs.trans inter_subset_left),
      (mem_cliqueEdges _ _).mpr (hs.trans inter_subset_right)⟩
  rw [hPQ, mem_singleton] at hsPQ
  have hse : s = e.val := congrArg Subtype.val hsPQ
  exact hse ▸ hvs (mem_singleton_self v)

theorem cliqueEdges_inter_singleton_iff (hr : 0 < r)
    (P : Block V q) (Q : Block V k) (e : Block V r) :
    cliqueEdges r P ∩ cliqueEdges r Q = {e} ↔ P.val ∩ Q.val = e.val :=
  ⟨vertices_inter_eq_of_cliqueEdges_singleton hr P Q e,
    cliqueEdges_inter_singleton_of_vertices P Q e⟩

theorem vertices_inter_eq_of_graph_inter_singleton (hr : 0 < r)
    (P : Block V q) (Q : Block V k) (B : Hypergraph V r) (e : Block V r)
    (hPB : cliqueEdges r P ∩ B = {e}) (hQ : cliqueEdges r Q ⊆ B)
    (heQ : e ∈ cliqueEdges r Q) : P.val ∩ Q.val = e.val := by
  apply vertices_inter_eq_of_cliqueEdges_singleton hr P Q e
  apply subset_antisymm
  · intro f hf
    have hfB : f ∈ cliqueEdges r P ∩ B :=
      mem_inter.mpr ⟨(mem_inter.mp hf).1, hQ (mem_inter.mp hf).2⟩
    exact hPB ▸ hfB
  · intro f hf
    have hfe : f = e := mem_singleton.mp hf
    subst f
    have heB : e ∈ cliqueEdges r P ∩ B := hPB ▸ mem_singleton_self e
    exact mem_inter.mpr ⟨(mem_inter.mp heB).1, heQ⟩

theorem clique_inter_card_lt_of_disjoint (P : Block V q) (Q : Block V k)
    (hPQ : Disjoint (cliqueEdges r P) (cliqueEdges r Q)) : (P.val ∩ Q.val).card < r := by
  by_contra h
  obtain ⟨s, hs, hsr⟩ := exists_subset_card_eq (Nat.le_of_not_gt h)
  exact disjoint_left.mp hPQ
    ((mem_cliqueEdges (⟨s, hsr⟩ : Block V r) P).mpr (hs.trans inter_subset_left))
    ((mem_cliqueEdges _ Q).mpr (hs.trans inter_subset_right))

theorem IsDecomposition.cliques_disjoint {G : Hypergraph V r} {D : Finset (Block V q)}
    (hD : IsDecomposition G D) {P Q : Block V q} (hP : P ∈ D) (hQ : Q ∈ D) (hPQ : P ≠ Q) :
    Disjoint (cliqueEdges r P) (cliqueEdges r Q) := by
  apply disjoint_left.mpr
  intro e heP heQ
  obtain ⟨R, _, hR⟩ := hD.unique (hD.clique_subset hP heP)
  exact hPQ ((hR P ⟨hP, (mem_cliqueEdges _ _).mp heP⟩).trans
    (hR Q ⟨hQ, (mem_cliqueEdges _ _).mp heQ⟩).symm)

theorem IsDecomposition.clique_inter_card_lt {G : Hypergraph V r} {D : Finset (Block V q)}
    (hD : IsDecomposition G D) {P Q : Block V q} (hP : P ∈ D) (hQ : Q ∈ D) (hPQ : P ≠ Q) :
    (P.val ∩ Q.val).card < r :=
  clique_inter_card_lt_of_disjoint P Q (hD.cliques_disjoint hP hQ hPQ)

end Arxiv2411_18291
