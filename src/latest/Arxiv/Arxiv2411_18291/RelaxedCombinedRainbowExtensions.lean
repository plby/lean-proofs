import Arxiv.Arxiv2411_18291.RelaxedRainbowRootPatterns
import Arxiv.Arxiv2411_18291.RainbowColourRelabeling

/-! # One logarithmic palette for all three relaxed rainbow extension properties -/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {U W : Type*} [Fintype U] [Fintype W] [DecidableEq W] {q r : ℕ}

def relaxedExtensionPaletteSize (n : ℕ) (S : ExchangeSystem W q (r + 1)) (N : Block W q) : ℕ :=
  (logarithmicColourTrialCount n (r + 1) * (q.choose (r + 1) - 1) + 1) +
    ((logarithmicColourTrialCount n q * (newEdges S.base.val S.graph).card + 1) +
      (logarithmicColourTrialCount n (S.base.val ∪ N.val).card *
        (newEdges (S.base.val ∪ N.val) S.graph).card + 1))

theorem combined_rainbow_extensions_relaxed_paper_threshold {n h : ℕ}
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (F₀ : Block U (r + 1)) (hU : Fintype.card U = q)
    {S : ExchangeSystem W q (r + 1)} {N : Block W q} {e₀ : Block W (r + 1)}
    (hpair : IsEliminationPair S N e₀) (hw : Fintype.card W ≤ (4 * q) ^ (2 * q))
    (hqh : q.choose (r + 1) ≤ h) (hSh : S.graph.card ≤ h)
    (hH : h ≤ 3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2)
    (K G : Hypergraph (Fin n) (r + 1))
    (hT : IsTypical K ((n : ℝ) ^ (-(1 / 10 : ℝ))) h)
    (hd : |density K - (n : ℝ) ^ (-paperAlpha q (r + 1))| ≤
      (n : ℝ) ^ (-(1 / 10 : ℝ)) * (n : ℝ) ^ (-paperAlpha q (r + 1)))
    (hGK : G ⊆ K)
    (hloss : ((K \ G).card : ℝ) ≤
      (n : ℝ) ^ (-(paperAlpha q (r + 1) / 60)) * K.card) :
    ∃ σ : Fin (relaxedExtensionPaletteSize n S N) → Equiv.Perm (Fin n),
      (∀ e : Block (Fin n) (r + 1),
        ((3 / 8 : ℝ) * density G ^ (q.choose (r + 1) - 1) *
          (n : ℝ) ^ (q - (r + 1))) / (q - (r + 1)).factorial <
            (rainbowPuncturedCliques (fun i => mapGraph (σ i).toEmbedding G) e q).card) ∧
      (∀ P : Block (Fin n) q, ∃ f : W ↪ Fin n, mapBlock f S.base = P ∧
        IsRainbow (fun i => mapGraph (σ i).toEmbedding G)
          (mapGraph f S.graph \ cliqueEdges (r + 1) P)) ∧
      (∀ P Q : Block (Fin n) q, ∀ d : Block (Fin n) (r + 1), P.val ∩ Q.val = d.val →
        ∃ f : W ↪ Fin n, mapBlock f S.base = P ∧ mapBlock f N = Q ∧
          IsRainbow (fun i => mapGraph (σ i).toEmbedding G)
            (mapGraph f S.graph \ (cliqueEdges (r + 1) P ∪ cliqueEdges (r + 1) Q))) := by
  classical
  let L₁ := logarithmicColourTrialCount n F₀.val.card
  let L₂ := logarithmicColourTrialCount n S.base.val.card
  let L₃ := logarithmicColourTrialCount n (S.base.val ∪ N.val).card
  let J₁ := Option (Fin L₁ × ↥(newEdges F₀.val (complete U (r + 1))))
  let J₂ := Option (Fin L₂ × ↥(newEdges S.base.val S.graph))
  let J₃ := Option (Fin L₃ × ↥(newEdges (S.base.val ∪ N.val) S.graph))
  let J := J₁ ⊕ (J₂ ⊕ J₃)
  have hcard : Fintype.card J = relaxedExtensionPaletteSize n S N := by
    simp only [J, J₁, J₂, J₃, Fintype.card_sum, Fintype.card_option, Fintype.card_prod,
      Fintype.card_fin, Fintype.card_coe, card_newEdges_complete_root F₀ hU,
      L₁, L₂, L₃, F₀.property, S.base.property]
    rfl
  let p : J ≃ Fin (relaxedExtensionPaletteSize n S N) := (Fintype.equivFin J).trans (finCongr hcard)
  let e₁ : J₁ ↪ J := Function.Embedding.inl
  let e₂ : J₂ ↪ J := Function.Embedding.inl.trans Function.Embedding.inr
  let e₃ : J₃ ↪ J := Function.Embedding.inr.trans Function.Embedding.inr
  let η₁ := e₁.trans p.toEmbedding
  let η₂ := e₂.trans p.toEmbedding
  let η₃ := e₃.trans p.toEmbedding
  obtain ⟨σ₁, hσ₁⟩ := exists_rainbow_punctured_cliques_relaxed_paper_threshold hqr hn hqh hH
    F₀ hU K G hT hd hGK hloss
  obtain ⟨σ₂, hσ₂⟩ := exists_rainbow_clique_roots_relaxed_paper_threshold hqr hn hqh hH hw
    S.graph hSh S.base K G hT hd hGK hloss
  obtain ⟨σ₃, hσ₃⟩ := exists_rainbow_pair_roots_relaxed_paper_threshold hqr hn hqh hH hw
    hpair hSh K G hT hd hGK hloss
  let σ : Fin (relaxedExtensionPaletteSize n S N) → Equiv.Perm (Fin n) :=
    fun i => Sum.elim σ₁ (Sum.elim σ₂ σ₃) (p.symm i)
  have hη₁ (i : J₁) : σ (η₁ i) = σ₁ i := by
    change Sum.elim σ₁ (Sum.elim σ₂ σ₃) (p.symm (p (Sum.inl i))) = σ₁ i
    rw [p.symm_apply_apply]
    rfl
  have hη₂ (i : J₂) : σ (η₂ i) = σ₂ i := by
    change Sum.elim σ₁ (Sum.elim σ₂ σ₃) (p.symm (p (Sum.inr (Sum.inl i)))) = σ₂ i
    rw [p.symm_apply_apply]
    rfl
  have hη₃ (i : J₃) : σ (η₃ i) = σ₃ i := by
    change Sum.elim σ₁ (Sum.elim σ₂ σ₃) (p.symm (p (Sum.inr (Sum.inr i)))) = σ₃ i
    rw [p.symm_apply_apply]
    rfl
  refine ⟨σ, ?_, ?_, ?_⟩
  · intro e
    have hc := card_le_card (rainbowPuncturedCliques_subset_reindex σ₁ σ G η₁ hη₁ e (q := q))
    exact (hσ₁ e).trans_le (by exact_mod_cast hc)
  · intro P
    obtain ⟨f, hf, hcol⟩ := hσ₂ P
    exact ⟨f, hf, hcol.permutation_reindex η₂ hη₂⟩
  · intro P Q d hPQ
    obtain ⟨f, hfP, hfQ, hcol⟩ := hσ₃ P Q d hPQ
    exact ⟨f, hfP, hfQ, hcol.permutation_reindex η₃ hη₃⟩

end Arxiv2411_18291
