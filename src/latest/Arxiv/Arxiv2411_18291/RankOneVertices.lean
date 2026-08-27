import Arxiv.Arxiv2411_18291.MaximumVertexPacking
import Arxiv.Arxiv2411_18291.GraphBoundedness

/-! # Rank-one graphs and their vertex sets -/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [DecidableEq V]

omit [DecidableEq V] in
theorem one_block_eq_singleton {e : Block V 1} {v : V} (hv : v ∈ e.val) :
    e.val = {v} := by
  apply (eq_of_subset_of_card_le (singleton_subset_iff.mpr hv) ?_).symm
  simp only [e.property, card_singleton, le_refl]

omit [DecidableEq V] in
theorem rankOne_isVertexPacking (G : Hypergraph V 1) : IsVertexPacking G := by
  intro e _ f _ hef
  apply disjoint_left.mpr
  intro v hve hvf
  exact hef (Subtype.ext ((one_block_eq_singleton hve).trans (one_block_eq_singleton hvf).symm))

theorem card_vertexSupport_rankOne (G : Hypergraph V 1) : (vertexSupport G).card = G.card := by
  simpa only [mul_one] using (rankOne_isVertexPacking G).card_vertexSupport

theorem vertexSupport_sdiff_rankOne (G K : Hypergraph V 1) :
    vertexSupport (G \ K) = vertexSupport G \ vertexSupport K := by
  ext v
  constructor
  · intro hv
    obtain ⟨e, he, hve⟩ := mem_biUnion.mp hv
    obtain ⟨heG, heK⟩ := mem_sdiff.mp he
    refine mem_sdiff.mpr ⟨subset_vertexSupport heG hve, ?_⟩
    intro hvK
    obtain ⟨f, hfK, hvf⟩ := mem_biUnion.mp hvK
    have hef : e = f := Subtype.ext
      ((one_block_eq_singleton hve).trans (one_block_eq_singleton hvf).symm)
    exact heK (hef.symm ▸ hfK)
  · intro hv
    obtain ⟨hvG, hvK⟩ := mem_sdiff.mp hv
    obtain ⟨e, heG, hve⟩ := mem_biUnion.mp hvG
    exact mem_biUnion.mpr ⟨e, mem_sdiff.mpr ⟨heG, fun heK =>
      hvK (subset_vertexSupport heK hve)⟩, hve⟩

variable [Fintype V]

theorem vertexSupport_cliqueSupport_one {q : ℕ} (D : Finset (Block V q)) :
    vertexSupport (cliqueSupport 1 D) = vertexSupport D := by
  ext v
  constructor
  · intro hv
    obtain ⟨e, he, hve⟩ := mem_biUnion.mp hv
    obtain ⟨Q, hQ, heQ⟩ := mem_biUnion.mp he
    exact subset_vertexSupport hQ ((mem_cliqueEdges _ _).mp heQ hve)
  · intro hv
    obtain ⟨Q, hQ, hvQ⟩ := mem_biUnion.mp hv
    let e : Block V 1 := ⟨{v}, card_singleton _⟩
    have heQ : e ∈ cliqueEdges 1 Q := (mem_cliqueEdges _ _).mpr
      (singleton_subset_iff.mpr hvQ)
    exact subset_vertexSupport (mem_biUnion.mpr ⟨Q, hQ, heQ⟩) (mem_singleton_self _)

theorem clique_vertices_subset_rankOne_support {G : Hypergraph V 1} {q : ℕ} {Q : Block V q}
    (hQ : cliqueEdges 1 Q ⊆ G) : Q.val ⊆ vertexSupport G := by
  intro v hv
  let e : Block V 1 := ⟨{v}, card_singleton _⟩
  exact subset_vertexSupport
    (hQ ((mem_cliqueEdges e Q).mpr (singleton_subset_iff.mpr hv))) (mem_singleton_self _)

omit [DecidableEq V] in
theorem card_rankOne_le (G : Hypergraph V 1) : G.card ≤ Fintype.card V := by
  classical
  have h := card_le_card (subset_univ (vertexSupport G))
  simpa only [card_vertexSupport_rankOne, card_univ] using h

theorem isGraphBounded_one_iff (G : Hypergraph V 1) (θ : ℝ) :
    IsGraphBounded G θ ↔ (G.card : ℝ) < θ * Fintype.card V := by
  constructor
  · intro h
    simpa only [empty_subset, filter_true] using h (⟨∅, rfl⟩ : Block V 0)
  · intro h f
    have hf : f.val = ∅ := card_eq_zero.mp f.property
    simpa only [hf, empty_subset, filter_true] using h

end Arxiv2411_18291
