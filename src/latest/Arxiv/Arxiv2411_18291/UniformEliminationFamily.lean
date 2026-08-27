import Arxiv.Arxiv2411_18291.CliquePairRootDegrees
import Arxiv.Arxiv2411_18291.UniformGreedyEmbedding
import Arxiv.Arxiv2411_18291.EliminationFamily

/-!
# Sparse elimination placements from balanced indexed roots

Prescribed clique pairs need only have the correct intersections and bounded
degrees in each indexed coordinate. No fixed repetition or multiplicity
bound is required. The construction is uniform over a polynomial density
interval, as needed when a representative is used for its whole group.
-/

open Finset Filter
open scoped Topology

noncomputable section

namespace Arxiv2411_18291

variable {W : Type*} [Fintype W] [DecidableEq W] {q r : ℕ}

theorem eventually_exists_uniform_elimination_family (S : ExchangeSystem W q (r + 1))
    (N : Block W q) (e : Block W (r + 1)) (hpair : IsEliminationPair S N e)
    (hqr : r + 1 ≤ q) {σ ρ : ℝ} (hσ : 0 < σ) (hσρ : σ ≤ ρ) (hρ1 : ρ < 1) :
    ∀ᶠ n : ℕ in atTop, ∀ θ : ℝ, (n : ℝ) ^ (-ρ) ≤ θ → θ ≤ (n : ℝ) ^ (-σ) →
      ∀ B : Hypergraph (Fin n) (r + 1), IsGraphBounded B θ →
      ∀ (J : Type) [Fintype J], ∀ P Q : J → Block (Fin n) q,
      (∀ i, cliqueEdges (r + 1) (P i) ∪ cliqueEdges (r + 1) (Q i) ⊆ B) →
      (∀ T : Block (Fin n) r, (familyDegree P T.val : ℝ) < θ * n) →
      (∀ T : Block (Fin n) r, (familyDegree Q T.val : ℝ) < θ * n) →
      (∀ i, ∃ d : Block (Fin n) (r + 1), (P i).val ∩ (Q i).val = d.val) →
      Nonempty (EliminationFamily S N B P Q (θ + S.graph.card * (4 * (r + 1).factorial * θ))) := by
  classical
  filter_upwards [eventually_exists_uniform_greedy_family S.graph (hpair.admissible hqr)
    hσ hσρ hρ1, eventually_ge_atTop (Fintype.card W)] with n hplace hn
  intro θ hlo hhi B hB J instJ P Q hsupport hP hQ hinter
  have hθ : 0 ≤ θ := (Real.rpow_nonneg (Nat.cast_nonneg n) _).trans hlo
  let t := Fintype.card J
  let enum : Fin t ≃ J := (Fintype.equivFin J).symm
  have hmaps (i : J) : ∃ φ : ↥(S.base.val ∪ N.val) ↪ Fin n,
      rootImage φ S.base subset_union_left = P i ∧ rootImage φ N subset_union_right = Q i := by
    obtain ⟨d, hd⟩ := hinter i
    exact hpair.root_map (P i) (Q i) d hd
  choose φ hφP hφQ using hmaps
  obtain ⟨f₀⟩ := Function.Embedding.nonempty_of_card_le
    (α := W) (β := Fin n) (by simpa only [Fintype.card_fin] using hn)
  let φ₀ : ↥(S.base.val ∪ N.val) ↪ Fin n :=
    (Function.Embedding.subtype (· ∈ S.base.val ∪ N.val)).trans f₀
  let Φ : ℕ → ↥(S.base.val ∪ N.val) ↪ Fin n := fun i =>
    if hi : i < t then φ (enum ⟨i, hi⟩) else φ₀
  have hΦ (i : Fin t) : Φ i = φ (enum i) := by dsimp only [Φ]; rw [dif_pos i.isLt]
  have hΦP (i : Fin t) : rootImage (Φ i) S.base subset_union_left = P (enum i) := by
    rw [hΦ i]
    exact hφP (enum i)
  have hΦQ (i : Fin t) : rootImage (Φ i) N subset_union_right = Q (enum i) := by
    rw [hΦ i]
    exact hφQ (enum i)
  have hP' (T : Block (Fin n) r) :
      (familyDegree (fun i : Fin t => P (enum i)) T.val : ℝ) < θ * Fintype.card (Fin n) := by
    simpa only [familyDegree_reindex, Fintype.card_fin] using hP T
  have hQ' (T : Block (Fin n) r) :
      (familyDegree (fun i : Fin t => Q (enum i)) T.val : ℝ) < θ * Fintype.card (Fin n) := by
    simpa only [familyDegree_reindex, Fintype.card_fin] using hQ T
  have hroots : ∀ f ∈ S.graph, ∀ hf : f.val ⊆ S.base.val ∪ N.val,
      IsEdgeFamilyBounded (fun i : Fin t => rootImage (Φ i) f hf) θ :=
    hpair.root_inputs_of_degrees (fun i => P (enum i)) (fun i => Q (enum i)) hP' hQ'
      (fun i => Φ i) hΦP hΦQ
  obtain ⟨Ψ, hΨ⟩ := hplace θ hlo hhi t Φ B hB hroots
  let Ξ : J → W ↪ Fin n := fun i => (Ψ (enum.symm i)).val
  have hroots' (i : Fin t) :
      mapBlock (Ψ i).val S.base = P (enum i) ∧ mapBlock (Ψ i).val N = Q (enum i) :=
    pair_extension_roots (Φ i) (hΦP i) (hΦQ i) (Ψ i)
  refine ⟨{
    embedding := Ξ
    positive_root := ?_
    negative_root := ?_
    root_support := hsupport
    avoids := fun i => hΨ.avoids (enum.symm i)
    disjoint := ?_
    bounded := ?_ }⟩
  · intro i
    simpa only [Equiv.apply_symm_apply] using (hroots' (enum.symm i)).1
  · intro i
    simpa only [Equiv.apply_symm_apply] using (hroots' (enum.symm i)).2
  · intro i j hij
    exact hΨ.disjoint (fun h => hij (enum.symm.injective h))
  · change IsGraphBounded (B ∪ univ.biUnion (fun i : J =>
      mapGraph (Ψ (enum.symm i)).val (newEdges (S.base.val ∪ N.val) S.graph))) _
    rw [biUnion_univ_reindex enum.symm
      (fun i : Fin t => mapGraph (Ψ i).val (newEdges (S.base.val ∪ N.val) S.graph))]
    exact hΨ.graphBounded hB (by positivity)

end Arxiv2411_18291
