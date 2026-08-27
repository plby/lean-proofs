import Arxiv.Arxiv2411_18291.CliqueCover
import Arxiv.Arxiv2411_18291.GreedyFamilyBounds
import Arxiv.Arxiv2411_18291.AsymptoticGreedyEmbedding

/-!
# Sparse placements of cliques on prescribed edges

The unrestricted greedy process can extend each edge of a sparse graph to
a larger clique. Distinct placed cliques are edge-disjoint, their only edges
in the original graph are their roots, and their union remains sparse.
Taking the larger clique size to be `q+r` supplies the geometry for the
absorber's local decoders.
-/

open Finset Filter

noncomputable section

namespace Arxiv2411_18291

variable {W V : Type*} [Fintype W] [Fintype V] [DecidableEq W] [DecidableEq V]
variable {q r t : ℕ}

theorem IsGreedyFamily.cliqueCover_complement (F₀ : Block W (r + 1))
    (hW : Fintype.card W = q) (E : Fin t → Block V (r + 1))
    (B : Hypergraph V (r + 1))
    (Ψ : (i : Fin t) → EmbeddingExtension (edgeRootMap F₀ (E i))) {L : ℝ}
    (hΨ : IsGreedyFamily (fun i => edgeRootMap F₀ (E i)) (complete W (r + 1)) B Ψ L)
    (hE : Function.Injective E) (hEB : ∀ i, E i ∈ B) :
    IsCliqueCover (complete V (r + 1) \ B) E (fun i => embeddingClique hW (Ψ i).val) := by
  apply hΨ.cliqueCover F₀ hW E _ B Ψ hE
  · intro i hi
    exact (Finset.mem_sdiff.mp hi).2 (hEB i)
  · intro i
    apply (mem_cliqueCandidateExtensions _ _ _ _ _).mpr
    apply (isPuncturedClique_iff _ _ _).mpr
    constructor
    · have he : mapBlock (Ψ i).val F₀ = E i :=
        (EmbeddingExtension.map_rootBlock (edgeRootMap F₀ (E i)) (Ψ i) F₀
          (Subset.refl _)).trans (rootImage_edgeRootMap F₀ (E i))
      calc
        _ = (mapBlock (Ψ i).val F₀).val := (congrArg Subtype.val he).symm
        _ ⊆ _ := map_subset_map.mpr (subset_univ _)
    · intro e he
      apply Finset.mem_sdiff.mpr
      refine ⟨mem_univ _, ?_⟩
      intro heB
      have hnew : e ∈ mapGraph (Ψ i).val (newEdges F₀.val (complete W (r + 1))) := by
        rw [map_newEdges_complete_eq_erase F₀ hW _ _
          (edgeRootMap_usedVertices F₀ (E i)) (Ψ i)]
        exact he
      exact disjoint_left.mp (hΨ.avoids i) hnew heB

theorem cliqueGraph_subset_base_union_new (F₀ : Block W (r + 1))
    (hW : Fintype.card W = q) (E : Fin t → Block V (r + 1))
    (B : Hypergraph V (r + 1))
    (Ψ : (i : Fin t) → EmbeddingExtension (edgeRootMap F₀ (E i))) (hEB : ∀ i, E i ∈ B) :
    cliqueCoverGraph (r := r) (fun i => embeddingClique hW (Ψ i).val) ⊆
      B ∪ greedyFamilyGraph F₀.val (complete W (r + 1)) (fun i => (Ψ i).val) := by
  intro e he
  obtain ⟨i, _, hei⟩ := mem_biUnion.mp he
  by_cases heE : e = E i
  · exact mem_union_left _ (heE ▸ hEB i)
  · apply mem_union_right
    apply mem_biUnion.mpr
    refine ⟨i, mem_univ _, ?_⟩
    rw [map_newEdges_complete_eq_erase F₀ hW _ _
      (edgeRootMap_usedVertices F₀ (E i)) (Ψ i)]
    exact mem_erase.mpr ⟨heE, hei⟩

omit [Fintype V] [DecidableEq V] [DecidableEq W] in
theorem eventually_exists_indexed_clique_placement (F₀ : Block W (r + 1))
    (hW : Fintype.card W = q) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    ∀ᶠ n : ℕ in atTop, ∀ t : ℕ, ∀ E : ℕ → Block (Fin n) (r + 1),
      ∀ B : Hypergraph (Fin n) (r + 1), IsGraphBounded B ((n : ℝ) ^ (-ρ)) →
      Function.Injective (fun i : Fin t => E i) → (∀ i < t, E i ∈ B) →
      IsEdgeFamilyBounded (fun i : Fin t => E i) ((n : ℝ) ^ (-ρ)) →
      ∃ Q : Fin t → Block (Fin n) q,
        IsCliqueCover (complete (Fin n) (r + 1) \ B) (fun i : Fin t => E i) Q ∧
        IsGraphBounded (cliqueCoverGraph (r := r) Q)
          ((1 + 4 * (r + 1).factorial * q.choose (r + 1)) * (n : ℝ) ^ (-ρ)) := by
  classical
  filter_upwards [eventually_exists_greedy_family (complete W (r + 1))
    (complete_root_admissible F₀) hρ hρ1] with n hgreedy
  intro t E B hB hE hEB hbound
  let Φ : ℕ → F₀.val ↪ Fin n := fun i => edgeRootMap F₀ (E i)
  have hroots : ∀ f ∈ complete W (r + 1), ∀ hf : f.val ⊆ F₀.val,
      IsEdgeFamilyBounded (fun i : Fin t => rootImage (Φ i) f hf) ((n : ℝ) ^ (-ρ)) := by
    intro f _ hf
    have hf0 : f = F₀ :=
      Subtype.ext (eq_of_subset_of_card_le hf (by rw [f.property, F₀.property]))
    subst f
    simpa only [Φ, rootImage_edgeRootMap] using hbound
  obtain ⟨Ψ, hΨ⟩ := hgreedy t Φ B hB hroots
  refine ⟨fun i => embeddingClique hW (Ψ i).val,
    hΨ.cliqueCover_complement F₀ hW (fun i => E i) B Ψ hE (fun i => hEB i i.isLt), ?_⟩
  have hL : 0 ≤ 4 * (r + 1).factorial * (n : ℝ) ^ (-ρ) := by positivity
  have hb := (hΨ.graphBounded hB hL).subgraph
    (cliqueGraph_subset_base_union_new F₀ hW (fun i => E i) B Ψ (fun i => hEB i i.isLt))
  have hc : (complete W (r + 1)).card = q.choose (r + 1) := by
    simp only [complete, card_univ, Block, Fintype.card_finset_len, hW]
  have heq : (n : ℝ) ^ (-ρ) + (complete W (r + 1)).card *
      (4 * (r + 1).factorial * (n : ℝ) ^ (-ρ)) =
      (1 + 4 * (r + 1).factorial * q.choose (r + 1)) * (n : ℝ) ^ (-ρ) := by
    rw [hc]
    ring
  simpa only [heq] using hb

omit [Fintype W] [Fintype V] [DecidableEq W] [DecidableEq V] in
theorem eventually_exists_clique_placement (hq : r + 1 ≤ q) {ρ : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    ∀ᶠ n : ℕ in atTop, ∀ B : Hypergraph (Fin n) (r + 1),
      IsGraphBounded B ((n : ℝ) ^ (-ρ)) →
      ∃ Q : B → Block (Fin n) q,
        IsCliqueCover (complete (Fin n) (r + 1) \ B) (fun e : B => e.val) Q ∧
        IsGraphBounded (cliqueCoverGraph (r := r) Q)
          ((1 + 4 * (r + 1).factorial * q.choose (r + 1)) * (n : ℝ) ^ (-ρ)) := by
  obtain ⟨s, _, hs⟩ := exists_subset_card_eq (s := (univ : Finset (Fin q)))
    (by simpa only [card_univ, Fintype.card_fin] using hq)
  let F₀ : Block (Fin q) (r + 1) := ⟨s, hs⟩
  filter_upwards [eventually_gt_atTop (0 : ℕ),
    eventually_exists_indexed_clique_placement F₀ (Fintype.card_fin q) hρ hρ1]
    with n hn hplace
  intro B hB
  rcases B.eq_empty_or_nonempty with hB0 | hBpos
  · subst B
    let Q : (∅ : Hypergraph (Fin n) (r + 1)) → Block (Fin n) q :=
      fun e => (notMem_empty _ e.property).elim
    have hQ : cliqueCoverGraph (r := r) Q = ∅ := by
      ext e
      simp only [cliqueCoverGraph, mem_biUnion, mem_univ, true_and, notMem_empty, iff_false]
      rintro ⟨i, _⟩
      exact notMem_empty _ i.property
    refine ⟨Q, ⟨fun e => (notMem_empty _ e.property).elim,
      fun i _ _ => (notMem_empty _ i.property).elim⟩, ?_⟩
    rw [hQ]
    have hx : (0 : ℝ) < n := by exact_mod_cast hn
    exact isGraphBounded_empty (by positivity) (by simpa only [Fintype.card_fin] using hn)
  · obtain ⟨e₀, _⟩ := hBpos
    let enum : Fin B.card ≃ B := B.equivFin.symm
    let E : ℕ → Block (Fin n) (r + 1) :=
      fun i => if hi : i < B.card then (enum ⟨i, hi⟩).val else e₀
    have hE (i : Fin B.card) : E i = (enum i).val := by
      dsimp [E]
      rw [if_pos i.isLt]
    have hEmem (i : Fin B.card) : E i ∈ B := hE i ▸ (enum i).property
    have hEinj : Function.Injective (fun i : Fin B.card => E i) := by
      intro i j hij
      apply enum.injective
      apply Subtype.ext
      simpa only [hE] using hij
    obtain ⟨Q, hQ, hb⟩ := hplace B.card E B hB hEinj (fun i hi => hEmem ⟨i, hi⟩)
      (hB.edgeFamily (fun i : Fin B.card => E i) hEmem hEinj)
    refine ⟨fun e => Q (enum.symm e), ?_, ?_⟩
    · constructor
      · intro e
        have heq : E (enum.symm e) = e.val := by rw [hE, Equiv.apply_symm_apply]
        simpa only [heq] using hQ.punctured (enum.symm e)
      · intro e f hef
        exact hQ.disjoint (fun h => hef (enum.symm.injective h))
    · rw [cliqueCoverGraph_reindex]
      exact hb

end Arxiv2411_18291
