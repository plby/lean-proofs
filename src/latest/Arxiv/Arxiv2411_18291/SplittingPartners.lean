import Arxiv.Arxiv2411_18291.SplittingNearIntersections

/-!
# The unique positive far partner of a negative near edge

Every edge outside the original graph in a negative near splitting clique
belongs to exactly one positive splitting clique, and that clique is far.
This is the partner used by the second elimination stage.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {W V : Type*} [Fintype W] [Fintype V] [DecidableEq W] [DecidableEq V]
variable {q r C : ℕ}

theorem ExchangeSystem.positive_erase_far (S : ExchangeSystem W q r)
    {P : Block W q} (hP : P ∈ S.positive.erase S.base) : P ∈ S.farCliques := by
  refine mem_sdiff.mpr ⟨mem_union_right _ hP, ?_⟩
  intro hn
  exact disjoint_left.mp S.disjoint (mem_erase.mp hP).2 (S.near_negative hn)

variable {S : ExchangeSystem W q (r + 1)} {D : Finset (Block V q)}
variable {B : Hypergraph V (r + 1)} {θ : ℝ}

theorem SplittingFamily.copy_index_unique (F : SplittingFamily S D B C θ)
    {s t : SignedCliqueSlots D C} {e : Block V (r + 1)}
    (hes : e ∈ mapGraph (F.embedding s) S.graph)
    (het : e ∈ mapGraph (F.embedding t) S.graph) (heB : e ∉ B) : s = t := by
  by_contra hst
  exact heB (F.copy_inter_subset hst (mem_inter.mpr ⟨hes, het⟩))

theorem SplittingFamily.negativeNear_positiveFar_partner (F : SplittingFamily S D B C θ)
    {P : Block V q} (hP : P ∈ F.negativeNear) {e : Block V (r + 1)}
    (heP : e ∈ cliqueEdges (r + 1) P) (heB : e ∉ B) :
    ∃ Q ∈ F.positiveFar, e ∈ cliqueEdges (r + 1) Q ∧
      ∀ R ∈ F.positiveCliques, e ∈ cliqueEdges (r + 1) R → R = Q := by
  obtain ⟨s, P₀, hP₀, hs, rfl⟩ := F.negativeNear_source hP
  have hes : e ∈ mapGraph (F.embedding s) S.graph :=
    mapGraph_mono (F.embedding s) (S.replacement_clique_subset (mem_filter.mp hP₀).1)
      (by rwa [map_cliqueEdges])
  obtain ⟨Q, ⟨hQ, heQ⟩, huniq⟩ := (S.map (F.embedding s)).positive_decomposition.unique hes
  have hQne : Q ≠ (S.map (F.embedding s)).base := by
    intro h
    change Q = mapBlock (F.embedding s) S.base at h
    exact heB (F.root_edges_subset s ((mem_cliqueEdges _ _).mpr (h ▸ heQ)))
  have hQpart : Q ∈ (S.map (F.embedding s)).positiveReplacement s.2.1 := by
    simpa [ExchangeSystem.positiveReplacement, hs] using mem_erase.mpr ⟨hQne, hQ⟩
  have hQsplit : Q ∈ F.positiveCliques := mem_biUnion.mpr ⟨s, mem_univ _, hQpart⟩
  have hQavoid : Disjoint (cliqueEdges (r + 1) Q) B := by
    have hQerase : Q ∈ mapGraph (F.embedding s) (S.positive.erase S.base) := by
      rw [mapGraph_erase]
      exact mem_erase.mpr ⟨hQne, hQ⟩
    obtain ⟨Q₀, hQ₀, rfl⟩ := (mem_mapGraph _ _ _).mp hQerase
    exact F.far_copy_disjoint s (S.positive_erase_far hQ₀)
  refine ⟨Q, mem_sdiff.mpr ⟨hQsplit, ?_⟩, (mem_cliqueEdges _ _).mpr heQ, ?_⟩
  · intro hn
    obtain ⟨f, hf⟩ := (mem_filter.mp hn).2
    exact disjoint_left.mp hQavoid (mem_inter.mp hf).1 (mem_inter.mp hf).2
  · intro R hR heR
    obtain ⟨t, _, ht⟩ := mem_biUnion.mp hR
    have het : e ∈ mapGraph (F.embedding t) S.graph :=
      (S.map (F.embedding t)).replacement_clique_subset
        ((S.map (F.embedding t)).positiveReplacement_subset _ ht) heR
    have hst := F.copy_index_unique hes het heB
    subst t
    have hRpos : R ∈ (S.map (F.embedding s)).positive := by
      have hRerase : R ∈ (S.map (F.embedding s)).positive.erase
          (S.map (F.embedding s)).base := by
        simpa [ExchangeSystem.positiveReplacement, hs] using ht
      exact (mem_erase.mp hRerase).2
    exact huniq R ⟨hRpos, (mem_cliqueEdges _ _).mp heR⟩

end Arxiv2411_18291
