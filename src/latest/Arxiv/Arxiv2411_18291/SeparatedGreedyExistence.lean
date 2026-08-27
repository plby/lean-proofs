import Arxiv.Arxiv2411_18291.SeparatedGreedyCandidates

/-!
# Greedy embeddings with separation between related roots

A finite numerical criterion produces actual root-preserving embeddings
whose new edges are disjoint and whose free vertices are disjoint whenever
the prescribed relation requires it. Candidate density one half changes the
output degree constant from `4*r!` to `8*r!`.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {W V : Type*} [Fintype W] [Fintype V] [DecidableEq W] [DecidableEq V]
variable {F : Finset W} {r : ℕ}

theorem exists_separated_greedy_family (Φ : ℕ → F ↪ V) (Rel : ℕ → ℕ → Prop)
    (H : Hypergraph W (r + 1)) (B : Hypergraph V (r + 1)) {θ : ℝ}
    (hB : IsGraphBounded B θ) (hθ : 0 ≤ θ) (t d : ℕ)
    (hrel : ∀ i < t, (priorRelated Rel i).card ≤ d)
    (hnpos : 0 < Fintype.card V) (hn : 4 * Fintype.card W ^ 2 ≤ Fintype.card V)
    (hsize : 4 * Fintype.card W * (d * Fintype.card W) ≤ Fintype.card V)
    (hsmall : H.card * (θ + H.card * (8 * (r + 1).factorial * θ)) ≤ 1 / 4)
    (hadm : IsAdmissible H F)
    (hroots : ∀ f ∈ H, ∀ hf : f.val ⊆ F,
      IsEdgeFamilyBounded (fun i : Fin t => rootImage (Φ i) f hf) θ)
    (hfailure : H.card * Fintype.card (Block V r) *
      Real.exp (-(4 * (r + 1).factorial * θ * Fintype.card V / 3)) < 1) :
    ∃ Ψ : (i : Fin t) → EmbeddingExtension (Φ i),
      IsGreedyFamily (fun i => Φ i) H B Ψ (8 * (r + 1).factorial * θ) ∧
      ∀ i j : Fin t, i < j → Rel i j →
        Disjoint ((univ \ F).map (Ψ i).val) ((univ \ F).map (Ψ j).val) := by
  have hL : 4 * ((r + 1).factorial : ℝ) * θ / (1 / 2) = 8 * (r + 1).factorial * θ := by ring
  have hquarter : (1 / 2 : ℝ) / 2 = 1 / 4 := by norm_num
  have hexp : (2 * ((r + 1).factorial : ℝ) * θ * Fintype.card V / (1 / 2)) / 3 =
      4 * (r + 1).factorial * θ * Fintype.card V / 3 := by ring
  obtain ⟨ω, Ψ, hΨ, hmem, hmatch⟩ := exists_prescribed_greedy_family Φ
    (separatedCandidates Φ Rel) H B hB hθ hθ (by norm_num : (0 : ℝ) < 1 / 2) hnpos
    (by simpa only [hL, hquarter] using hsmall) t
    (separatedCandidates_lower_bound Φ Rel H _ hrel hn hsize) hadm hroots
    (by simpa only [hexp] using hfailure)
  exact ⟨Ψ, by simpa only [hL] using hΨ,
    separatedCandidates_disjoint Φ Rel ω Ψ hmem hmatch⟩

end Arxiv2411_18291
