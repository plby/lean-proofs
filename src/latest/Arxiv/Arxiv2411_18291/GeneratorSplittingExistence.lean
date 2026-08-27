import Arxiv.Arxiv2411_18291.GeneratorSplittingBounds
import Arxiv.Arxiv2411_18291.AsymptoticGreedyEmbedding

/-!
# Constructing exchange copies on all generators

The original boundary bound controls every family of prescribed root
edges. The ordinary greedy embedding theorem therefore places one copy
per generator, without an initial multiplicity assumption.
-/

open Finset Filter
open scoped Topology

noncomputable section

namespace Arxiv2411_18291

variable {W : Type*} [Fintype W] [DecidableEq W] {q r : ℕ}

theorem exists_generator_splitting_of_greedy (S : ExchangeSystem W q (r + 1))
    (hqr : r + 1 ≤ q) (n : ℕ) {θ : ℝ} (hθ : 0 ≤ θ) (hn : Fintype.card W ≤ n)
    (hplace : ∀ t : ℕ, ∀ Φ : ℕ → S.base.val ↪ Fin n,
      ∀ B : Hypergraph (Fin n) (r + 1), IsGraphBounded B θ →
      (∀ e ∈ S.graph, ∀ he : e.val ⊆ S.base.val,
        IsEdgeFamilyBounded (fun i : Fin t => rootImage (Φ i) e he) θ) →
      ∃ Ψ : (i : Fin t) → EmbeddingExtension (Φ i),
        IsGreedyFamily (fun i => Φ i) S.graph B Ψ (4 * (r + 1).factorial * θ))
    (D : Finset (Block (Fin n) q)) (hD : IsCliqueFamilyBounded r D θ) :
    Nonempty (GeneratorSplitting S D (θ + S.graph.card * (4 * (r + 1).factorial * θ))) := by
  classical
  let t := Fintype.card D
  let enum : Fin t ≃ D := (Fintype.equivFin D).symm
  obtain ⟨f₀⟩ := Function.Embedding.nonempty_of_card_le
    (α := W) (β := Fin n) (by simpa only [Fintype.card_fin] using hn)
  let φ₀ : S.base.val ↪ Fin n := (Function.Embedding.subtype (· ∈ S.base.val)).trans f₀
  let Φ : ℕ → S.base.val ↪ Fin n := fun i =>
    if hi : i < t then edgeRootMap S.base (enum ⟨i, hi⟩).val else φ₀
  have hΦ (i : Fin t) : Φ i = edgeRootMap S.base (enum i).val := by
    dsimp only [Φ]
    rw [dif_pos i.isLt]
  have hrep (P : Block (Fin n) q) : (univ.filter fun i : Fin t => (enum i).val = P).card ≤ 1 := by
    apply card_le_one.mpr
    intro i hi j hj
    exact enum.injective (Subtype.ext ((mem_filter.mp hi).2.trans (mem_filter.mp hj).2.symm))
  have hroots : ∀ e ∈ S.graph, ∀ he : e.val ⊆ S.base.val,
      IsEdgeFamilyBounded (fun i : Fin t => rootImage (Φ i) e he) (θ) := by
    intro e _ he
    have hsub (i : Fin t) : (rootImage (Φ i) e he).val ⊆ (enum i).val.val := by
      calc
        _ ⊆ usedVertices (Φ i) := rootImage_subset_usedVertices (Φ i) e he
        _ = _ := by rw [hΦ i, edgeRootMap_usedVertices]
    simpa only [Nat.cast_one, one_mul] using hD.repeated_edgeFamily hqr
      (fun i : Fin t => (enum i).val) (fun i => (enum i).property) (by decide : 0 < 1)
      hrep (fun i : Fin t => rootImage (Φ i) e he) hsub
  obtain ⟨Ψ, hΨ⟩ := hplace t Φ (cliqueSupport (r + 1) D) hD.support_graphBounded hroots
  let f : D → W ↪ Fin n := fun Q => (Ψ (enum.symm Q)).val
  have hbase (i : Fin t) : mapBlock (Ψ i).val S.base = (enum i).val := by
    rw [EmbeddingExtension.map_rootBlock (Φ i) (Ψ i) S.base Subset.rfl, hΦ i,
      rootImage_edgeRootMap]
  refine ⟨{
    embedding := f
    base := ?_
    avoids := fun Q => hΨ.avoids (enum.symm Q)
    disjoint := ?_
    bounded := ?_ }⟩
  · intro Q
    dsimp only [f]
    rw [hbase, Equiv.apply_symm_apply]
  · intro P Q hPQ
    exact hΨ.disjoint (fun h => hPQ (enum.symm.injective h))
  · change IsGraphBounded (cliqueSupport (r + 1) D ∪ univ.biUnion (fun Q : D =>
      mapGraph (Ψ (enum.symm Q)).val (newEdges S.base.val S.graph))) _
    rw [biUnion_univ_reindex enum.symm
      (fun i : Fin t => mapGraph (Ψ i).val (newEdges S.base.val S.graph))]
    exact hΨ.graphBounded hD.support_graphBounded (by positivity)


theorem eventually_exists_generator_splitting (S : ExchangeSystem W q (r + 1))
    (hqr : r + 1 ≤ q) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    ∀ᶠ n : ℕ in atTop, ∀ D : Finset (Block (Fin n) q),
      IsCliqueFamilyBounded r D ((n : ℝ) ^ (-ρ)) →
      Nonempty (GeneratorSplitting S D ((n : ℝ) ^ (-ρ) + S.graph.card *
        (4 * (r + 1).factorial * (n : ℝ) ^ (-ρ)))) := by
  have hadm := admissible_clique_root S.graph S.base hqr
    (S.positive_decomposition.clique_subset S.base_mem)
  filter_upwards [eventually_exists_greedy_family S.graph hadm hρ hρ1,
    eventually_ge_atTop (Fintype.card W)] with n hplace hn
  intro D hD
  exact exists_generator_splitting_of_greedy S hqr n
    (Real.rpow_nonneg (Nat.cast_nonneg n) _) hn hplace D hD

end Arxiv2411_18291
