import Arxiv.Arxiv2411_18291.ExplicitSeparatedGreedyNumerics
import Arxiv.Arxiv2411_18291.SeparatedGreedyExistence

/-! # Actual finite greedy embeddings with prescribed free-vertex separation -/

open Finset

noncomputable section

namespace Arxiv2411_18291

theorem exists_absorber_separated_greedy_family_paper_threshold
    {W : Type*} [Fintype W] [DecidableEq W] {F : Finset W} {q r n d : ℕ}
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hw : Fintype.card W ≤ (4 * q) ^ (8 * q))
    (H : Hypergraph W (r + 1)) (hH : H.card ≤ (4 * q) ^ (8 * q))
    (hadm : IsAdmissible H F) (hd : d ≤ (4 * q) ^ (8 * q))
    {A : ℝ} (hA : 1 ≤ A) (hAb : 2 * A ≤ (4 * q : ℝ) ^ (8 * q))
    (t : ℕ) (Φ : ℕ → F ↪ Fin n) (Rel : ℕ → ℕ → Prop)
    (B : Hypergraph (Fin n) (r + 1))
    (hB : IsGraphBounded B (A * (n : ℝ) ^ (-(paperAlpha q (r + 1) / 3))))
    (hrel : ∀ i < t, (priorRelated Rel i).card ≤ d)
    (hroots : ∀ f ∈ H, ∀ hf : f.val ⊆ F,
      IsEdgeFamilyBounded (fun i : Fin t => rootImage (Φ i) f hf)
        (A * (n : ℝ) ^ (-(paperAlpha q (r + 1) / 3)))) :
    ∃ Ψ : (i : Fin t) → EmbeddingExtension (Φ i),
      IsGreedyFamily (fun i => Φ i) H B Ψ
        (8 * (r + 1).factorial * (A * (n : ℝ) ^ (-(paperAlpha q (r + 1) / 3)))) ∧
      ∀ i j : Fin t, i < j → Rel i j →
        Disjoint ((univ \ F).map (Ψ i).val) ((univ \ F).map (Ψ j).val) := by
  obtain ⟨hnpos, hsize, hsep, hsmall, hfailure⟩ :=
    absorber_separated_greedy_numerics hqr hn hw hH hd hA hAb
  have hAnonneg : 0 ≤ A := le_trans zero_le_one hA
  exact exists_separated_greedy_family Φ Rel H B hB (by positivity) t d hrel
    (by simpa only [Fintype.card_fin] using hnpos)
    (by simpa only [Fintype.card_fin] using hsize)
    (by simpa only [Fintype.card_fin] using hsep) hsmall hadm hroots
    (by simpa only [Block, Fintype.card_finset_len, Fintype.card_fin] using hfailure)

end Arxiv2411_18291
