import Arxiv.Arxiv2411_18291.GeneratorSplittingMultiplicity

/-!
# Exact intersections within one split root class

Distinct split cliques containing the same original-support edge intersect
precisely in that edge. Their other edges are new and lie in distinct
exchange copies. A group may therefore use one of its own cliques as a
representative for pair elimination, without another bridge construction.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {W V : Type*} [Fintype W] [DecidableEq W] [Fintype V] [DecidableEq V]
variable {q r : ℕ} {S : ExchangeSystem W q (r + 1)} {D : Finset (Block V q)} {θ : ℝ}

theorem GeneratorSplitting.same_root_inter (F : GeneratorSplitting S D θ)
    {A : Finset (Block W q)} (hA : IsExchangeFamily S A)
    {P Q : Block V q} (hP : P ∈ F.cliques) (hQ : Q ∈ F.cliques) (hPQ : P ≠ Q)
    {e : Block V (r + 1)} (heD : e ∈ cliqueSupport (r + 1) D)
    (heP : e ∈ cliqueEdges (r + 1) P) (heQ : e ∈ cliqueEdges (r + 1) Q) :
    P.val ∩ Q.val = e.val := by
  obtain ⟨R, _, hR⟩ := mem_biUnion.mp hP
  obtain ⟨T, _, hT⟩ := mem_biUnion.mp hQ
  have hRT : R ≠ T := by
    intro h
    subst T
    have hcard : ((S.map (F.embedding R)).replacementCliques.filter
        fun P => e.val ⊆ P.val).card ≤ 1 :=
      (F.copy_count_original R e heD).trans (by split_ifs <;> omega)
    exact hPQ (card_le_one.mp hcard P (mem_filter.mpr ⟨hR, (mem_cliqueEdges _ _).mp heP⟩)
      Q (mem_filter.mpr ⟨hT, (mem_cliqueEdges _ _).mp heQ⟩))
  apply vertices_inter_eq_of_cliqueEdges_singleton (Nat.succ_pos r) P Q e
  apply Subset.antisymm
  · intro f hf
    obtain ⟨hfP, hfQ⟩ := mem_inter.mp hf
    by_cases hfD : f ∈ cliqueSupport (r + 1) D
    · apply mem_singleton.mpr
      exact card_le_one.mp (F.clique_inter_card_le_one hA hP)
        f (mem_inter.mpr ⟨hfP, hfD⟩) e (mem_inter.mpr ⟨heP, heD⟩)
    · exact (hRT (F.copy_index_unique
        ((S.map (F.embedding R)).replacement_clique_subset hR hfP)
        ((S.map (F.embedding T)).replacement_clique_subset hT hfQ) hfD)).elim
  · exact singleton_subset_iff.mpr (mem_inter.mpr ⟨heP, heQ⟩)

end Arxiv2411_18291
