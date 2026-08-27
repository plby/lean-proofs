import Arxiv.Arxiv2411_18291.FiniteFocusingFamily
import Arxiv.Arxiv2411_18291.RelaxedFocusingCounts

/-! # Actual focusing families with edge multiplicity at most one -/

open Finset

noncomputable section

namespace Arxiv2411_18291

theorem exists_sparse_focusing_family_with_cap_paper_threshold {q r n : ℕ}
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (B E : Hypergraph (Fin n) (r + 1))
    (hB : IsGraphBounded B ((n : ℝ) ^ (-paperRho q (r + 1))))
    (hcount : ∀ e ∈ B \ E, (n : ℝ) ^ (-paperFocusingExponent q (r + 1)) *
      (n : ℝ) ^ (q - (r + 1)) ≤ (puncturedCliques E e q).card) :
    ∃ F : Finset (Block (Fin n) q),
      IsCliqueFamilyBounded r F ((n : ℝ) ^ (-(7 * paperAlpha q (r + 1) / 10))) ∧
      (∀ e : Block (Fin n) (r + 1), (F.filter fun Q => e.val ⊆ Q.val).card ≤ 1) ∧
      ∀ J : Block (Fin n) (r + 1) → ℤ, (∀ e, e ∉ B → J e = 0) →
        IntegrallyDecomposable q J →
        ∃ K : Block (Fin n) (r + 1) → ℤ, GeneratedBy F (J - K) ∧
          (∀ e, e ∉ E → K e = 0) ∧ IntegrallyDecomposable q K := by
  have hd : Disjoint (B \ E) E :=
    disjoint_left.mpr (fun _ he hE => (mem_sdiff.mp he).2 hE)
  obtain ⟨Q, hQ, hbound⟩ := exists_focusing_clique_cover_paper_threshold hqr hn
    E (B \ E) hd (hB.subgraph sdiff_subset) hcount
  exact exists_focusing_family_of_clique_cover_with_cap B E Q hQ hbound

theorem exists_sparse_coloured_focusing_with_cap_paper_threshold {I : Type*} [Fintype I]
    {q r n H : ℕ} (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hqh : q.choose (r + 1) ≤ H)
    (hH : H ≤ 3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2)
    (K G : Hypergraph (Fin n) (r + 1))
    (hd : |density K - (n : ℝ) ^ (-paperAlpha q (r + 1))| ≤
      (n : ℝ) ^ (-(1 / 10 : ℝ)) * (n : ℝ) ^ (-paperAlpha q (r + 1)))
    (hGK : G ⊆ K)
    (hloss : ((K \ G).card : ℝ) ≤
      (n : ℝ) ^ (-(paperAlpha q (r + 1) / 60)) * K.card)
    (σ : I → Equiv.Perm (Fin n))
    (hcount : ∀ e : Block (Fin n) (r + 1),
      ((3 / 8 : ℝ) * density G ^ (q.choose (r + 1) - 1) *
        (n : ℝ) ^ (q - (r + 1))) / (q - (r + 1)).factorial ≤
          (rainbowPuncturedCliques (fun i => mapGraph (σ i).toEmbedding G) e q).card)
    (B : Hypergraph (Fin n) (r + 1))
    (hB : IsGraphBounded B ((n : ℝ) ^ (-paperRho q (r + 1)))) :
    ∃ F : Finset (Block (Fin n) q),
      IsCliqueFamilyBounded r F ((n : ℝ) ^ (-(7 * paperAlpha q (r + 1) / 10))) ∧
      (∀ e : Block (Fin n) (r + 1), (F.filter fun Q => e.val ⊆ Q.val).card ≤ 1) ∧
      ∀ J : Block (Fin n) (r + 1) → ℤ, (∀ e, e ∉ B → J e = 0) →
        IntegrallyDecomposable q J →
        ∃ J' : Block (Fin n) (r + 1) → ℤ, GeneratedBy F (J - J') ∧
          (∀ e, e ∉ permutedUnion σ G → J' e = 0) ∧ IntegrallyDecomposable q J' := by
  apply exists_sparse_focusing_family_with_cap_paper_threshold hqr hn B (permutedUnion σ G) hB
  intro e _
  exact coloured_punctured_clique_count_relaxed_paper_threshold
    hqr hn hqh hH K G hd hGK hloss σ hcount e

end Arxiv2411_18291
