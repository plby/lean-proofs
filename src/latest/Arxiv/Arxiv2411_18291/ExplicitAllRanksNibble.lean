import Arxiv.Arxiv2411_18291.ExplicitNibble
import Arxiv.Arxiv2411_18291.ExplicitPairNibble
import Arxiv.Arxiv2411_18291.NibbleBinomialScales

/-! # Full Lemma 2.4 at the printed size threshold, in every positive rank -/

open Finset

noncomputable section

namespace Arxiv2411_18291

theorem exists_nibble_paper_threshold (q r n : ℕ) (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n)
    (G : Hypergraph (Fin n) (r + 1)) (H : Finset (Block (Fin n) q))
    (hG : (1 / 2 : ℝ) * (n.choose (r + 1) : ℝ) < G.card)
    (hHG : ∀ Q ∈ H, cliqueEdges (r + 1) Q ⊆ G)
    (hd : ∀ e ∈ G,
      |((H.filter fun Q => e.val ⊆ Q.val).card : ℝ) - (n.choose (q - (r + 1)) : ℝ) / 2| ≤
        (n : ℝ) ^ (-(1 / 3 : ℝ)) * ((n.choose (q - (r + 1)) : ℝ) / 2)) :
    ∃ C : Finset (Block (Fin n) q), C ⊆ H ∧
      IsDecomposition (cliqueSupport (r + 1) C) C ∧
        IsGraphBounded (G \ cliqueSupport (r + 1) C)
          ((n : ℝ) ^ (-(3 * q.choose (r + 1) * paperRho q (r + 1)))) := by
  by_cases hq2 : q = 2
  · subst q
    have hr0 : r = 0 := by omega
    subst r
    have hdegrees : ∀ e ∈ G,
        |((H.filter fun Q => e.val ⊆ Q.val).card : ℝ) - (n : ℝ) / 2| ≤
          (n : ℝ) ^ (-(1 / 3 : ℝ)) * ((n : ℝ) / 2) := by
      simpa only [Nat.reduceAdd, Nat.reduceSub, Nat.choose_one_right] using hd
    obtain ⟨C, hCH, hC, hbound⟩ :=
      exists_rankOne_pair_nibble_paper_threshold n hn G H hHG hdegrees
    refine ⟨C, hCH, hC, ?_⟩
    convert hbound using 1
    norm_num [paperRho]
  · apply exists_nibble_paper_threshold_of_three_le q r n hqr _ hn G H hG hHG hd
    by_cases hr0 : r = 0
    · simp only [hr0, Nat.zero_add, Nat.choose_one_right]
      omega
    · exact three_le_clique_size (by omega) hqr

end Arxiv2411_18291
