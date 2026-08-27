import Arxiv.Arxiv2411_18291.FiniteFocusingNumerics
import Arxiv.Arxiv2411_18291.FiniteFocusingCounts
import Arxiv.Arxiv2411_18291.SparseFocusingFamily

/-! # Actual sparse focusing families at the paper's size threshold -/

open Finset

noncomputable section

namespace Arxiv2411_18291

theorem exists_focusing_clique_cover_paper_threshold {q r n : ℕ}
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (R B : Hypergraph (Fin n) (r + 1)) (hBR : Disjoint B R)
    (hB : IsGraphBounded B ((n : ℝ) ^ (-paperRho q (r + 1))))
    (hcount : ∀ e ∈ B, (n : ℝ) ^ (-paperFocusingExponent q (r + 1)) *
      (n : ℝ) ^ (q - (r + 1)) ≤ (puncturedCliques R e q).card) :
    ∃ Q : B → Block (Fin n) q, IsCliqueCover R (fun e => e.val) Q ∧
      IsGraphBounded (cliqueCoverGraph (r := r) Q)
        ((n : ℝ) ^ (-(7 * paperAlpha q (r + 1) / 10))) := by
  have hnpos : 0 < n :=
    Nat.zero_lt_one.trans ((paperSizeThreshold_one_lt hqr).trans_le hn)
  obtain ⟨Q, hQ, hbound⟩ := exists_sparse_clique_cover_of_numerics hqr.le hnpos
    (paper_focusing_smallness hqr hn) (paper_focusing_failure_lt_one hqr hn)
    R B hBR hB hcount
  exact ⟨Q, hQ, hbound.mono (focusing_degree_bound_paper_threshold hqr hn)⟩

theorem exists_sparse_focusing_family_paper_threshold {q r n : ℕ}
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (B E : Hypergraph (Fin n) (r + 1))
    (hB : IsGraphBounded B ((n : ℝ) ^ (-paperRho q (r + 1))))
    (hcount : ∀ e ∈ B \ E, (n : ℝ) ^ (-paperFocusingExponent q (r + 1)) *
      (n : ℝ) ^ (q - (r + 1)) ≤ (puncturedCliques E e q).card) :
    ∃ F : Finset (Block (Fin n) q),
      IsCliqueFamilyBounded r F ((n : ℝ) ^ (-(7 * paperAlpha q (r + 1) / 10))) ∧
      ∀ J : Block (Fin n) (r + 1) → ℤ, (∀ e, e ∉ B → J e = 0) →
        IntegrallyDecomposable q J →
        ∃ K : Block (Fin n) (r + 1) → ℤ, GeneratedBy F (J - K) ∧
          (∀ e, e ∉ E → K e = 0) ∧ IntegrallyDecomposable q K := by
  have hd : Disjoint (B \ E) E :=
    disjoint_left.mpr (fun _ he hE => (mem_sdiff.mp he).2 hE)
  obtain ⟨Q, hQ, hbound⟩ := exists_focusing_clique_cover_paper_threshold hqr hn
    E (B \ E) hd (hB.subgraph sdiff_subset) hcount
  exact exists_focusing_family_of_clique_cover B E Q hQ hbound

theorem exists_sparse_coloured_focusing_paper_threshold {I : Type*} [Fintype I]
    {q r n : ℕ} (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (K G : Hypergraph (Fin n) (r + 1))
    (hd : |density K - (n : ℝ) ^ (-paperAlpha q (r + 1))| ≤
      (n : ℝ) ^ (-(1 / 10 : ℝ)) * (n : ℝ) ^ (-paperAlpha q (r + 1)))
    (hGK : G ⊆ K)
    (hloss : ((K \ G).card : ℝ) ≤
      (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) * K.card)
    (σ : I → Equiv.Perm (Fin n))
    (hcount : ∀ e : Block (Fin n) (r + 1),
      ((3 / 8 : ℝ) * density G ^ (q.choose (r + 1) - 1) *
        (n : ℝ) ^ (q - (r + 1))) / (q - (r + 1)).factorial ≤
          (rainbowPuncturedCliques (fun i => mapGraph (σ i).toEmbedding G) e q).card)
    (B : Hypergraph (Fin n) (r + 1))
    (hB : IsGraphBounded B ((n : ℝ) ^ (-paperRho q (r + 1)))) :
    ∃ F : Finset (Block (Fin n) q),
      IsCliqueFamilyBounded r F ((n : ℝ) ^ (-(7 * paperAlpha q (r + 1) / 10))) ∧
      ∀ J : Block (Fin n) (r + 1) → ℤ, (∀ e, e ∉ B → J e = 0) →
        IntegrallyDecomposable q J →
        ∃ J' : Block (Fin n) (r + 1) → ℤ, GeneratedBy F (J - J') ∧
          (∀ e, e ∉ permutedUnion σ G → J' e = 0) ∧ IntegrallyDecomposable q J' := by
  apply exists_sparse_focusing_family_paper_threshold hqr hn B (permutedUnion σ G) hB
  intro e _
  exact coloured_punctured_clique_count_paper_threshold hqr hn K G hd hGK hloss σ hcount e

end Arxiv2411_18291
