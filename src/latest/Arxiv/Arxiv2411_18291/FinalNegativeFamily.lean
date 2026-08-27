import Arxiv.Arxiv2411_18291.SecondElimination

/-!
# The final negative family is a true decomposition

Retain the negative far splitting cliques and the good negative cliques
of the first stage, then add the second stage's negative cliques. The
proved partner geometry makes this whole family edge-disjoint. Its union
therefore has a true clique decomposition and avoids the original graph.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}

theorem isDecomposition_cliqueSupport_of_pairwise (D : Finset (Block V q))
    (hD : (D : Set (Block V q)).Pairwise
      (fun Q R => Disjoint (cliqueEdges r Q) (cliqueEdges r R))) :
    IsDecomposition (cliqueSupport r D) D := by
  apply isDecomposition_of_unique
  · intro Q hQ e he
    exact mem_biUnion.mpr ⟨Q, hQ, he⟩
  · intro e he
    obtain ⟨Q, hQ, heQ⟩ := mem_biUnion.mp he
    refine ⟨Q, ⟨hQ, (mem_cliqueEdges _ _).mp heQ⟩, ?_⟩
    intro R hR
    by_contra hRQ
    exact disjoint_left.mp (hD hR.1 hQ hRQ) ((mem_cliqueEdges _ _).mpr hR.2) heQ

variable {W U : Type*} [Fintype W] [Fintype U] [DecidableEq W] [DecidableEq U] {C : ℕ}
variable {S : ExchangeSystem W q (r + 1)} {D : Finset (Block V q)}
variable {B : Hypergraph V (r + 1)} {θ θ' θ'' : ℝ}
variable {T : ExchangeSystem U q (r + 1)} {N : Block U q} {e₀ : Block U (r + 1)}
variable (F : SplittingFamily S D B C θ)
variable (E : EliminationFamily T N F.graph F.pairPositive F.pairNegative θ')

theorem retainedNegative_pairwise (hpair : IsEliminationPair T N e₀) :
    (retainedNegative F E : Set (Block V q)).Pairwise
      (fun R Q => Disjoint (cliqueEdges (r + 1) R) (cliqueEdges (r + 1) Q)) := by
  intro R hR Q hQ hRQ
  rcases mem_union.mp hR with hRf | hRg <;> rcases mem_union.mp hQ with hQf | hQg
  · exact F.negativeFar_disjoint_negative hRf (mem_sdiff.mp hQf).1 hRQ
  · apply (first_good_negative_disjoint_splitting F E hQg _).symm
    rw [F.cliques_eq_signs]
    exact mem_union_right _ (mem_sdiff.mp hRf).1
  · apply first_good_negative_disjoint_splitting F E hRg
    rw [F.cliques_eq_signs]
    exact mem_union_right _ (mem_sdiff.mp hQf).1
  · exact E.goodNegative_disjoint hpair hRg (mem_filter.mp hQg).1 hRQ

variable (L : FurtherEliminationPairs F E)
variable (G : EliminationFamily T N E.graph L.positive (fun i : E.badNegative => i.val) θ'')

theorem further_negative_pairwise (hpair : IsEliminationPair T N e₀) :
    (G.negativeCliques : Set (Block V q)).Pairwise
      (fun R Q => Disjoint (cliqueEdges (r + 1) R) (cliqueEdges (r + 1) Q)) :=
  G.negative_pairwise_of_root_inter hpair (L.root_overlap_cover hpair)

theorem further_negative_disjoint_retained (hpair : IsEliminationPair T N e₀)
    {R : Block V q} (hR : R ∈ G.negativeCliques) :
    Disjoint (cliqueEdges (r + 1) R) (cliqueSupport (r + 1) (retainedNegative F E)) :=
  G.negative_disjoint_previous hpair (retainedNegative_support F E hpair)
    (L.root_inter_retained hpair) hR

theorem further_negative_disjoint_splitting (hpair : IsEliminationPair T N e₀)
    {R : Block V q} (hR : R ∈ G.negativeCliques) :
    Disjoint (cliqueEdges (r + 1) R) F.graph :=
  G.negative_disjoint_previous hpair subset_union_left L.root_inter_splitting hR

def finalNegative : Finset (Block V q) := retainedNegative F E ∪ G.negativeCliques

theorem finalNegative_pairwise (hpair : IsEliminationPair T N e₀) :
    (finalNegative F E L G : Set (Block V q)).Pairwise
      (fun R Q => Disjoint (cliqueEdges (r + 1) R) (cliqueEdges (r + 1) Q)) := by
  intro R hR Q hQ hRQ
  rcases mem_union.mp hR with hRo | hRn <;> rcases mem_union.mp hQ with hQo | hQn
  · exact retainedNegative_pairwise F E hpair hRo hQo hRQ
  · apply (Disjoint.mono_right _ (further_negative_disjoint_retained F E L G hpair hQn)).symm
    intro e he
    exact mem_biUnion.mpr ⟨R, hRo, he⟩
  · apply Disjoint.mono_right _ (further_negative_disjoint_retained F E L G hpair hRn)
    intro e he
    exact mem_biUnion.mpr ⟨Q, hQo, he⟩
  · exact further_negative_pairwise F E L G hpair hRn hQn hRQ

theorem finalNegative_decomposition (hpair : IsEliminationPair T N e₀) :
    IsDecomposition (cliqueSupport (r + 1) (finalNegative F E L G)) (finalNegative F E L G) :=
  isDecomposition_cliqueSupport_of_pairwise _ (finalNegative_pairwise F E L G hpair)

theorem finalNegative_avoids_original (hpair : IsEliminationPair T N e₀) :
    Disjoint (cliqueSupport (r + 1) (finalNegative F E L G)) B := by
  apply disjoint_left.mpr
  intro e he heB
  obtain ⟨R, hR, heR⟩ := mem_biUnion.mp he
  rcases mem_union.mp hR with hOld | hNew
  · rcases mem_union.mp hOld with hFar | hGood
    · exact disjoint_left.mp (F.negativeFar_disjoint_original hFar) heR heB
    · exact disjoint_left.mp (mem_filter.mp hGood).2 heR (mem_union_left _ heB)
  · exact disjoint_left.mp (further_negative_disjoint_splitting F E L G hpair hNew)
      heR (mem_union_left _ heB)

theorem finalNegative_support (hpair : IsEliminationPair T N e₀) :
    cliqueSupport (r + 1) (finalNegative F E L G) ⊆ G.graph := by
  intro e he
  obtain ⟨R, hR, heR⟩ := mem_biUnion.mp he
  rcases mem_union.mp hR with hOld | hNew
  · exact mem_union_left _ (retainedNegative_support F E hpair (mem_biUnion.mpr ⟨R, hOld, heR⟩))
  · apply G.cliques_support hpair
    refine mem_biUnion.mpr ⟨R, ?_, heR⟩
    rw [G.cliques_eq_signs]
    exact mem_union_right _ hNew

theorem finalNegative_bounded (hpair : IsEliminationPair T N e₀) :
    IsGraphBounded (cliqueSupport (r + 1) (finalNegative F E L G)) θ'' :=
  G.bounded.subgraph (finalNegative_support F E L G hpair)

end Arxiv2411_18291
