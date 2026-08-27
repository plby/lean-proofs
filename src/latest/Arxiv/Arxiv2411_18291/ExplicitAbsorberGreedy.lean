import Arxiv.Arxiv2411_18291.ExplicitAbsorberGreedyNumerics
import Arxiv.Arxiv2411_18291.GreedyEmbeddingExistence

/-! # Actual greedy placements at the absorber's finite working scale -/

noncomputable section

namespace Arxiv2411_18291

theorem exists_absorber_greedy_family_paper_threshold
    {W : Type*} [Fintype W] [DecidableEq W] {F : Finset W} {q r n : ℕ}
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hw : Fintype.card W ≤ (4 * q) ^ (8 * q))
    (H : Hypergraph W (r + 1)) (hH : H.card ≤ (4 * q) ^ (8 * q))
    (hadm : IsAdmissible H F) {A : ℝ}
    (hA : 1 ≤ A) (hAb : A ≤ (4 * q : ℝ) ^ (8 * q))
    (t : ℕ) (Φ : ℕ → F ↪ Fin n) (B : Hypergraph (Fin n) (r + 1))
    (hB : IsGraphBounded B (A * (n : ℝ) ^ (-(paperAlpha q (r + 1) / 3))))
    (hroots : ∀ f ∈ H, ∀ hf : f.val ⊆ F,
      IsEdgeFamilyBounded (fun i : Fin t => rootImage (Φ i) f hf)
        (A * (n : ℝ) ^ (-(paperAlpha q (r + 1) / 3)))) :
    ∃ Ψ : (i : Fin t) → EmbeddingExtension (Φ i),
      IsGreedyFamily (fun i => Φ i) H B Ψ
        (4 * (r + 1).factorial * (A * (n : ℝ) ^ (-(paperAlpha q (r + 1) / 3)))) := by
  obtain ⟨hnpos, hsize, hsmall, hfailure⟩ := absorber_greedy_numerics hqr hn hw hH hA hAb
  have hAnonneg : 0 ≤ A := le_trans zero_le_one hA
  exact exists_greedy_family Φ H B hB (by positivity)
    (by simpa only [Fintype.card_fin] using hsize)
    (by simpa only [Fintype.card_fin] using hnpos) hsmall t hadm hroots
    (by simpa only [Block, Fintype.card_finset_len, Fintype.card_fin] using hfailure)

end Arxiv2411_18291
