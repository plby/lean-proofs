import Arxiv.Arxiv2411_18291.SplittingNearFar

/-!
# Exact intersections between near splitting cliques

Two distinct near splitting cliques sharing an edge intersect in exactly
that edge's vertices. The proof uses the separation of free vertices for
copies whose roots overlap. This supplies the geometric prerequisite for
placing an exchange on an opposite-sign cancellation pair.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {W V : Type*} [Fintype W] [Fintype V] [DecidableEq W] [DecidableEq V]
variable {q r C : ℕ} {S : ExchangeSystem W q (r + 1)} {D : Finset (Block V q)}
variable {B : Hypergraph V (r + 1)} {θ : ℝ}

theorem SplittingFamily.near_copies_inter (F : SplittingFamily S D B C θ)
    {A : Finset (Block W q)} (hA : IsExchangeFamily S A)
    {s t : SignedCliqueSlots D C} (hst : s ≠ t)
    {P Q : Block W q} (hP : P ∈ S.nearCliques) (hQ : Q ∈ S.nearCliques)
    {e : Block V (r + 1)} (heP : e ∈ cliqueEdges (r + 1) (mapBlock (F.embedding s) P))
    (heQ : e ∈ cliqueEdges (r + 1) (mapBlock (F.embedding t) Q)) :
    (mapBlock (F.embedding s) P).val ∩ (mapBlock (F.embedding t) Q).val = e.val := by
  have hPg := S.replacement_clique_subset (mem_filter.mp hP).1
  have hQg := S.replacement_clique_subset (mem_filter.mp hQ).1
  have heB : e ∈ B := F.copy_inter_subset hst (mem_inter.mpr
    ⟨mapGraph_mono (F.embedding s) hPg (by rwa [map_cliqueEdges]),
      mapGraph_mono (F.embedding t) hQg (by rwa [map_cliqueEdges])⟩)
  have hPint := F.near_copy_inter hA s ⟨P, hP⟩
  have hQint := F.near_copy_inter hA t ⟨Q, hQ⟩
  have hePs : e = mapBlock (F.embedding s) (hA.nearRoot (Nat.succ_pos r) ⟨P, hP⟩) := by
    have he := mem_inter.mpr ⟨heP, heB⟩
    rwa [hPint, mem_singleton] at he
  have heQt : e = mapBlock (F.embedding t) (hA.nearRoot (Nat.succ_pos r) ⟨Q, hQ⟩) := by
    have he := mem_inter.mpr ⟨heQ, heB⟩
    rwa [hQint, mem_singleton] at he
  rw [← hePs] at hPint
  rw [← heQt] at hQint
  have heRs : e ∈ cliqueEdges (r + 1) (mapBlock (F.embedding s) S.base) := by
    have he := mem_inter.mpr ⟨heP, heB⟩
    rw [F.copy_clique_inter s P hPg] at he
    exact (mem_inter.mp he).2
  have heRt : e ∈ cliqueEdges (r + 1) (mapBlock (F.embedding t) S.base) := by
    have he := mem_inter.mpr ⟨heQ, heB⟩
    rw [F.copy_clique_inter t Q hQg] at he
    exact (mem_inter.mp he).2
  have hroots : r + 1 ≤ (s.1.val.val ∩ t.1.val.val).card := by
    rw [← F.base s, ← F.base t]
    simpa only [e.property] using card_le_card
      (subset_inter ((mem_cliqueEdges _ _).mp heRs) ((mem_cliqueEdges _ _).mp heRt))
  have hPt := vertices_inter_eq_of_graph_inter_singleton (Nat.succ_pos r)
    (mapBlock (F.embedding s) P) (mapBlock (F.embedding t) S.base) B e
    hPint (F.root_edges_subset t) heRt
  have hQs := vertices_inter_eq_of_graph_inter_singleton (Nat.succ_pos r)
    (mapBlock (F.embedding t) Q) (mapBlock (F.embedding s) S.base) B e
    hQint (F.root_edges_subset s) heRs
  apply subset_antisymm
  · intro v hv
    obtain ⟨hvP, hvQ⟩ := mem_inter.mp hv
    by_contra hve
    have hvs : v ∉ (mapBlock (F.embedding s) S.base).val := by
      intro h
      exact hve (hQs ▸ mem_inter.mpr ⟨hvQ, h⟩)
    have hvt : v ∉ (mapBlock (F.embedding t) S.base).val := by
      intro h
      exact hve (hPt ▸ mem_inter.mpr ⟨hvP, h⟩)
    exact disjoint_left.mp (F.free_disjoint s t hst hroots)
      (mem_free_image_of_not_root (F.embedding s) P.val S.base.val hvP hvs)
      (mem_free_image_of_not_root (F.embedding t) Q.val S.base.val hvQ hvt)
  · exact subset_inter ((mem_cliqueEdges _ _).mp heP) ((mem_cliqueEdges _ _).mp heQ)

theorem SplittingFamily.negative_near_inter (F : SplittingFamily S D B C θ)
    {A : Finset (Block W q)} (hA : IsExchangeFamily S A)
    {P Q : Block V q} (hP : P ∈ F.negativeNear) (hQ : Q ∈ F.negativeNear)
    (hPQ : P ≠ Q) {e : Block V (r + 1)}
    (heP : e ∈ cliqueEdges (r + 1) P) (heQ : e ∈ cliqueEdges (r + 1) Q) :
    P.val ∩ Q.val = e.val := by
  obtain ⟨s, P₀, hP₀, _, rfl⟩ := F.negativeNear_source hP
  obtain ⟨t, Q₀, hQ₀, _, rfl⟩ := F.negativeNear_source hQ
  by_cases hst : s = t
  · subst t
    have hP' : mapBlock (F.embedding s) P₀ ∈ (S.map (F.embedding s)).negative :=
      (mem_mapGraph _ _ _).mpr ⟨P₀, S.near_negative hP₀, rfl⟩
    have hQ' : mapBlock (F.embedding s) Q₀ ∈ (S.map (F.embedding s)).negative :=
      (mem_mapGraph _ _ _).mpr ⟨Q₀, S.near_negative hQ₀, rfl⟩
    exact (disjoint_left.mp ((S.map (F.embedding s)).negative_decomposition.cliques_disjoint
      hP' hQ' hPQ) heP heQ).elim
  · exact F.near_copies_inter hA hst hP₀ hQ₀ heP heQ

theorem SplittingFamily.opposite_near_inter (F : SplittingFamily S D B C θ)
    {A : Finset (Block W q)} (hA : IsExchangeFamily S A)
    {P Q : Block V q} (hP : P ∈ F.negativeNear) (hQ : Q ∈ F.positiveNear)
    {e : Block V (r + 1)} (heP : e ∈ cliqueEdges (r + 1) P)
    (heQ : e ∈ cliqueEdges (r + 1) Q) : P.val ∩ Q.val = e.val := by
  obtain ⟨s, P₀, hP₀, hs, rfl⟩ := F.negativeNear_source hP
  obtain ⟨t, Q₀, hQ₀, ht, rfl⟩ := F.positiveNear_source hQ
  have hst : s ≠ t := by
    intro h
    have heq : false = true := hs.symm.trans ((congrArg (fun u => u.2.1) h).trans ht)
    exact Bool.false_ne_true heq
  exact F.near_copies_inter hA hst hP₀ hQ₀ heP heQ

end Arxiv2411_18291
