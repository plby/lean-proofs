import Arxiv.Arxiv2411_18291.EliminationPlacements
import Arxiv.Arxiv2411_18291.SplittingFamily

/-!
# A placed family of cancellation exchanges

The family records actual vertex embeddings, both prescribed roots, and
disjoint new edges outside the previous graph. Its existence theorem is
uniform over arbitrary finite index types, so it applies directly to the
sets of cancellation pairs in both elimination stages.
-/

open Finset Filter

noncomputable section

namespace Arxiv2411_18291

variable {W V : Type*} [Fintype W] [Fintype V] [DecidableEq W] [DecidableEq V]
variable {I : Type*} [Fintype I] {q r : ℕ}

structure EliminationFamily (S : ExchangeSystem W q (r + 1)) (N : Block W q)
    (B : Hypergraph V (r + 1)) (P Q : I → Block V q) (θ : ℝ) where
  embedding : I → W ↪ V
  positive_root : ∀ i, mapBlock (embedding i) S.base = P i
  negative_root : ∀ i, mapBlock (embedding i) N = Q i
  root_support : ∀ i, cliqueEdges (r + 1) (P i) ∪ cliqueEdges (r + 1) (Q i) ⊆ B
  avoids : ∀ i, Disjoint (mapGraph (embedding i) (newEdges (S.base.val ∪ N.val) S.graph)) B
  disjoint : Pairwise fun i j => Disjoint
    (mapGraph (embedding i) (newEdges (S.base.val ∪ N.val) S.graph))
    (mapGraph (embedding j) (newEdges (S.base.val ∪ N.val) S.graph))
  bounded : IsGraphBounded
    (B ∪ univ.biUnion fun i => mapGraph (embedding i) (newEdges (S.base.val ∪ N.val) S.graph)) θ

omit [Fintype V] [DecidableEq V] [Fintype I] in
theorem eventually_exists_elimination_family (S : ExchangeSystem W q (r + 1))
    (N : Block W q) (e : Block W (r + 1)) (hpair : IsEliminationPair S N e)
    (hqr : r + 1 ≤ q) (M : ℕ) (hM : 0 < M) {A ρ : ℝ}
    (hA : 1 ≤ A) (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    ∀ᶠ n : ℕ in atTop, ∀ D : Finset (Block (Fin n) q),
      ∀ B : Hypergraph (Fin n) (r + 1),
      IsCliqueFamilyBounded r D (A * (n : ℝ) ^ (-ρ)) →
      IsGraphBounded B (A * (n : ℝ) ^ (-ρ)) → cliqueSupport (r + 1) D ⊆ B →
      (∀ f : Block (Fin n) (r + 1), (D.filter fun Q => f.val ⊆ Q.val).card ≤ M) →
      ∀ (J : Type) [Fintype J], ∀ P Q : J → Block (Fin n) q,
      (∀ i, P i ∈ D) → (∀ i, Q i ∈ D) → (Function.Injective fun i => (P i, Q i)) →
      (∀ i, ∃ d : Block (Fin n) (r + 1), (P i).val ∩ (Q i).val = d.val) →
      Nonempty (EliminationFamily S N B P Q
        (A * (n : ℝ) ^ (-ρ) + S.graph.card *
          (8 * (r + 1).factorial * (((q.choose (r + 1) * M : ℕ) : ℝ) *
            A * (n : ℝ) ^ (-ρ))))) := by
  filter_upwards [eventually_exists_elimination_placements S N e hpair hqr M hM hA hρ hρ1]
    with n hplace
  intro D B hD hB hsupport hmult J instJ P Q hP hQ hinj hinter
  let enum : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
  obtain ⟨Φ, Ψ, hΨ, hroots, hbound⟩ := hplace D B hD hB hmult (Fintype.card J)
    (fun i => P (enum i)) (fun i => Q (enum i)) (fun i => hP (enum i)) (fun i => hQ (enum i))
    (hinj.comp enum.injective) (fun i => hinter (enum i))
  let Ξ : J → W ↪ Fin n := fun i => (Ψ (enum.symm i)).val
  have hΞ (i : Fin (Fintype.card J)) : Ξ (enum i) = (Ψ i).val :=
    congrArg (fun j => (Ψ j).val) (enum.symm_apply_apply i)
  refine ⟨⟨Ξ, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro i
    simpa only [Equiv.apply_symm_apply] using (hroots (enum.symm i)).1
  · intro i
    simpa only [Equiv.apply_symm_apply] using (hroots (enum.symm i)).2
  · intro i f hf
    rcases mem_union.mp hf with hp | hq
    · exact hsupport (mem_biUnion.mpr ⟨P i, hP i, hp⟩)
    · exact hsupport (mem_biUnion.mpr ⟨Q i, hQ i, hq⟩)
  · intro i
    exact hΨ.avoids (enum.symm i)
  · intro i j hij
    exact hΨ.disjoint (fun h => hij (enum.symm.injective h))
  · have hgraph : (univ.biUnion fun i : Fin (Fintype.card J) =>
        mapGraph (Ψ i).val (newEdges (S.base.val ∪ N.val) S.graph)) =
        univ.biUnion (fun i : J => mapGraph (Ξ i) (newEdges (S.base.val ∪ N.val) S.graph)) := by
      calc
        _ = univ.biUnion (fun i : Fin (Fintype.card J) =>
            mapGraph (Ξ (enum i)) (newEdges (S.base.val ∪ N.val) S.graph)) := by
          apply congrArg (fun f : Fin (Fintype.card J) → Hypergraph (Fin n) (r + 1) =>
            univ.biUnion f)
          funext i
          rw [hΞ i]
        _ = _ := biUnion_univ_reindex enum
          (fun i => mapGraph (Ξ i) (newEdges (S.base.val ∪ N.val) S.graph))
    unfold greedyFamilyGraph at hbound
    rw [hgraph] at hbound
    exact hbound

end Arxiv2411_18291
