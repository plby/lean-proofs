import Arxiv.Arxiv2411_18291.ExplicitEliminationPlacements
import Arxiv.Arxiv2411_18291.EliminationFamily

/-! # Finite cancellation families for arbitrary finite index types -/

open Finset

noncomputable section

namespace Arxiv2411_18291

theorem exists_elimination_family_paper_threshold
    {W : Type*} [Fintype W] [DecidableEq W] {q r n : ℕ}
    (S : ExchangeSystem W q (r + 1)) (N : Block W q) (e : Block W (r + 1))
    (hpair : IsEliminationPair S N e) (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hw : Fintype.card W ≤ (4 * q) ^ (2 * q))
    (hS : S.graph.card ≤ (4 * q) ^ (2 * q)) (M : ℕ) (hM : 0 < M)
    {A ρ : ℝ} (hA : 1 ≤ A)
    (hAb : ((q.choose (r + 1) * M : ℕ) : ℝ) * A ≤ (4 * q : ℝ) ^ (24 * q))
    (hρ : paperAlpha q (r + 1) / 3 ≤ ρ) (hρhalf : ρ ≤ 1 / 2)
    (D : Finset (Block (Fin n) q)) (B : Hypergraph (Fin n) (r + 1))
    (hD : IsCliqueFamilyBounded r D (A * (n : ℝ) ^ (-ρ)))
    (hB : IsGraphBounded B (A * (n : ℝ) ^ (-ρ)))
    (hsupport : cliqueSupport (r + 1) D ⊆ B)
    (hmult : ∀ f : Block (Fin n) (r + 1), (D.filter fun Q => f.val ⊆ Q.val).card ≤ M)
    (J : Type) [Fintype J] (P Q : J → Block (Fin n) q)
    (hP : ∀ i, P i ∈ D) (hQ : ∀ i, Q i ∈ D)
    (hinj : Function.Injective fun i => (P i, Q i))
    (hinter : ∀ i, ∃ d : Block (Fin n) (r + 1), (P i).val ∩ (Q i).val = d.val) :
    Nonempty (EliminationFamily S N B P Q
      (A * (n : ℝ) ^ (-ρ) + S.graph.card *
        (8 * (r + 1).factorial * (((q.choose (r + 1) * M : ℕ) : ℝ) *
          A * (n : ℝ) ^ (-ρ))))) := by
  let enum : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
  obtain ⟨Φ, Ψ, hΨ, hroots, hbound⟩ := exists_elimination_placements_paper_threshold
    S N e hpair hqr hn hw hS M hM hA hAb hρ hρhalf D B hD hB hmult (Fintype.card J)
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
