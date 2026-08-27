import Arxiv.Arxiv2411_18291.GreedyEmbeddingProcess

/-!
# Legal extensions from a prescribed candidate set

A candidate set of size at least `η*n^m` loses at most `|H|*θ*n^m`
embeddings to a `θ`-bounded forbidden graph. In particular, if that loss
is at most half the initial count, at least `(η/2)*n^m` legal candidates
remain. The forbidden density is independent of the density of root maps.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {W V : Type*} [Fintype W] [Fintype V] [DecidableEq W] [DecidableEq V]
variable {F : Finset W} {r n : ℕ}

def candidateLegalExtensions (φ : F ↪ V) (H : Hypergraph W (r + 1))
    (B : Hypergraph V (r + 1)) (A : Finset (EmbeddingExtension φ)) :
    Finset (EmbeddingExtension φ) := A \ forbiddenExtensions φ H B

@[simp] theorem mem_candidateLegalExtensions (φ : F ↪ V) (H : Hypergraph W (r + 1))
    (B : Hypergraph V (r + 1)) (A : Finset (EmbeddingExtension φ)) (a : EmbeddingExtension φ) :
    a ∈ candidateLegalExtensions φ H B A ↔ a ∈ A ∧ a ∈ legalExtensions φ H B := by
  simp only [candidateLegalExtensions, legalExtensions, mem_sdiff, mem_univ, true_and]

theorem candidateLegalExtensions_card_half (φ : F ↪ V) (H : Hypergraph W (r + 1))
    (B : Hypergraph V (r + 1)) (A : Finset (EmbeddingExtension φ)) {θ η : ℝ}
    (hB : IsGraphBounded B θ) (hθ : 0 ≤ θ)
    (hA : η * (Fintype.card V : ℝ) ^ (Fintype.card W - F.card) ≤ A.card)
    (hsmall : H.card * θ ≤ η / 2) :
    (η / 2) * (Fintype.card V : ℝ) ^ (Fintype.card W - F.card) ≤
      (candidateLegalExtensions φ H B A).card := by
  have hbad := (forbiddenExtensions_card_le φ H B hB hθ).trans
    (mul_le_mul_of_nonneg_right hsmall (pow_nonneg (Nat.cast_nonneg _) _))
  have hc : (A.card : ℝ) ≤ (candidateLegalExtensions φ H B A).card +
      (forbiddenExtensions φ H B).card := by
    exact_mod_cast (card_le_card_sdiff_add_card (s := A) (t := forbiddenExtensions φ H B))
  linarith

theorem candidateLegalExtensions_nonempty (φ : F ↪ V) (H : Hypergraph W (r + 1))
    (B : Hypergraph V (r + 1)) (A : Finset (EmbeddingExtension φ)) {θ η : ℝ}
    (hB : IsGraphBounded B θ) (hθ : 0 ≤ θ) (hη : 0 < η) (hn : 0 < Fintype.card V)
    (hA : η * (Fintype.card V : ℝ) ^ (Fintype.card W - F.card) ≤ A.card)
    (hsmall : H.card * θ ≤ η / 2) : (candidateLegalExtensions φ H B A).Nonempty := by
  apply card_pos.mp
  have hV : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
  have hp : 0 < (η / 2) * (Fintype.card V : ℝ) ^ (Fintype.card W - F.card) := by positivity
  exact_mod_cast hp.trans_le (candidateLegalExtensions_card_half φ H B A hB hθ hA hsmall)

theorem historyCandidateLegal_card_half (φ : F ↪ V) (H : Hypergraph W (r + 1))
    (B : Hypergraph V (r + 1)) (h : FiniteHistoryProcess.History (EmbeddingState W V) n)
    (A : Finset (EmbeddingExtension φ)) {θB L η : ℝ}
    (hB : IsGraphBounded B θB) (hθB : 0 ≤ θB) (hL : 0 ≤ L)
    (hA : η * (Fintype.card V : ℝ) ^ (Fintype.card W - F.card) ≤ A.card)
    (hsmall : H.card * (θB + H.card * L) ≤ η / 2) (hgood : historyGood H F L h) :
    (η / 2) * (Fintype.card V : ℝ) ^ (Fintype.card W - F.card) ≤
      (candidateLegalExtensions φ H (historyForbidden H B F h) A).card :=
  candidateLegalExtensions_card_half φ H _ A (historyForbidden_bounded H B h hB hL hgood)
    (by positivity) hA hsmall

end Arxiv2411_18291
